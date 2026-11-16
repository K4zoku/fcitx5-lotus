/*
 * SPDX-FileCopyrightText: 2026 Kazoku <k4zoku@disr.it>
 *
 * SPDX-License-Identifier: GPL-3.0-or-later
 */

/**
 * Wayland wire backend. This is a separate preload library from the API hook.
 * Its only application-facing interception point is the Wayland Unix socket.
 * All normal Wayland traffic, including SCM_RIGHTS, is forwarded unchanged.
 */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include "lotus-apphook-target.h"
#include "lotus-apphook-sequence.h"

#include <algorithm>
#include <array>
#include <atomic>
#include <cerrno>
#include <condition_variable>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <dlfcn.h>
#include <fcntl.h>
#include <memory>
#include <mutex>
#include <poll.h>
#include <string>
#include <string_view>
#include <sys/eventfd.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/un.h>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <unistd.h>

extern "C" int lotus_apphook_resume_child_runtime() __attribute__((visibility("hidden")));

namespace lotus::apphook {
    namespace {

        constexpr size_t kReadChunk      = 16384;
        constexpr size_t kMaxWireMessage = 65535;
        constexpr size_t kFdBudget       = 64;

        uint32_t         word(const uint8_t* p) {
            uint32_t result;
            std::memcpy(&result, p, sizeof(result));
            return result;
        }

        void putWord(uint8_t* p, uint32_t value) {
            std::memcpy(p, &value, sizeof(value));
        }

        bool isWaylandSocket(const sockaddr* address, socklen_t length) {
            if (!address || address->sa_family != AF_UNIX || length <= offsetof(sockaddr_un, sun_path))
                return false;
            const auto*  un  = reinterpret_cast<const sockaddr_un*>(address);
            const size_t max = std::min<size_t>(length - offsetof(sockaddr_un, sun_path), sizeof(un->sun_path));
            if (!max || un->sun_path[0] == '\0')
                return false;
            const size_t n = strnlen(un->sun_path, max);
            if (n == max)
                return false;
            std::string_view path(un->sun_path, n);
            std::string_view display = std::getenv("WAYLAND_DISPLAY") ? std::getenv("WAYLAND_DISPLAY") : "wayland-0";
            if (path == display)
                return true;
            if (!display.empty() && display[0] == '/')
                return false;
            const size_t separator = path.rfind('/');
            return separator != std::string_view::npos && path.substr(separator + 1) == display;
        }

        struct Keyboard {
            bool      focused   = false;
            uint32_t  surface   = 0;
            uintptr_t token     = 0;
            uint32_t  serial    = 0;
            uint32_t  time      = 0;
            uint32_t  depressed = 0;
            uint32_t  latched   = 0;
            uint32_t  locked    = 0;
            uint32_t  group     = 0;
            // Standard XKB modifier indices until a compositor keymap is observed.
            uint32_t shiftIndex = 0, ctrlIndex = 2, altIndex = 3, superIndex = 6;
        };

        enum class Object : uint8_t {
            Registry,
            Seat,
            Keyboard
        };

        struct Connection {
            int                                    upstream = -1;
            int                                    relay    = -1;
            int                                    notify   = -1;
            std::atomic<bool>                      alive{true};
            std::unordered_map<uint32_t, Object>   objects;
            std::unordered_set<uint32_t>           seatGlobals;
            std::unordered_map<uint32_t, Keyboard> keyboards;
            std::mutex                             startMutex;
            std::condition_variable                startCv;
            bool                                   started = false;
            bool                                   abort   = false;
            std::atomic<int>                       threads{2};
            ~Connection() {
                if (upstream >= 0)
                    close(upstream);
                if (relay >= 0)
                    close(relay);
                if (notify >= 0)
                    close(notify);
            }
        };

        struct Registry {
            const pid_t                              pid = getpid();
            std::mutex                               mutex;
            std::vector<std::shared_ptr<Connection>> connections;
            Connection*                              lastInput         = nullptr;
            uint32_t                                 lastInputKeyboard = 0;
            uintptr_t                                nextToken         = 0;
        };

        std::atomic<Registry*> activeRegistry{nullptr};

        Registry&              registry() {
            const pid_t pid     = getpid();
            Registry*   current = activeRegistry.load(std::memory_order_acquire);
            if (current && current->pid == pid)
                return *current;
            // Fork children cannot reuse a parent's mutex or IPC worker. Start a new
            // generation only when the child opens its own Wayland connection.
            auto* fresh = new Registry;
            for (;;) {
                Registry* expected = current;
                if (activeRegistry.compare_exchange_strong(expected, fresh, std::memory_order_acq_rel)) {
                    if (current && current->pid != pid)
                        (void)lotus_apphook_resume_child_runtime();
                    return *fresh;
                }
                current = expected;
                if (current && current->pid == pid) {
                    delete fresh;
                    return *current;
                }
            }
        }

        struct FocusState {
            FocusCandidates candidate;
            bool            available = false;
            bool            focused   = false;
        };

        FocusState focusLocked(const Registry& r) {
            FocusState result;
            for (const auto& conn : r.connections) {
                if (!conn->alive.load(std::memory_order_acquire))
                    continue;
                for (const auto& [id, key] : conn->keyboards) {
                    (void)id;
                    result.available = true;
                    if (key.focused && key.surface && key.token) {
                        result.focused = true;
                        ++result.candidate.count;
                        result.candidate.target = {HookBackend::Wayland, conn.get(), key.token};
                    }
                }
            }
            if (result.candidate.count > 1 && r.lastInput) {
                for (const auto& conn : r.connections) {
                    if (conn.get() != r.lastInput || !conn->alive.load())
                        continue;
                    const auto it = conn->keyboards.find(r.lastInputKeyboard);
                    if (it != conn->keyboards.end() && it->second.focused && it->second.surface && it->second.token) {
                        result.candidate = {{HookBackend::Wayland, conn.get(), it->second.token}, 1};
                    }
                    break;
                }
            }
            return result;
        }

        void updateReadiness() {
            auto&      r = registry();
            FocusState state;
            {
                std::scoped_lock lock(r.mutex);
                state = focusLocked(r);
            }
            noteWaylandKeyboardAvailable(state.available);
            noteWaylandFocus(state.focused);
        }

        void cancelFocus(const Connection* conn, uintptr_t token) {
            if (!token)
                return;
            auto&            state = runtime();
            std::scoped_lock lock(state.mutex);
            for (auto it = state.pending.begin(); it != state.pending.end();) {
                auto& task = *it;
                if (task->target.backend == HookBackend::Wayland && task->target.connection == conn && task->target.focused == token) {
                    task->cancelled.store(true, std::memory_order_release);
                    finishLocked(task, -ECANCELED);
                    it = state.pending.erase(it);
                } else {
                    ++it;
                }
            }
        }

        bool getText(const uint8_t* buf, size_t len, size_t offset, std::string_view& text, size_t& next) {
            if (offset + 4 > len)
                return false;
            const size_t size = word(buf + offset);
            if (!size || size > len - offset - 4 || buf[offset + 4 + size - 1] != 0)
                return false;
            text                = std::string_view(reinterpret_cast<const char*>(buf + offset + 4), size - 1);
            const size_t padded = (size + 3) & ~size_t(3);
            if (padded > len - offset - 4)
                return false;
            next = offset + 4 + padded;
            return true;
        }

        /** Process complete protocol messages; never change the original bytes. */
        void observe(const std::shared_ptr<Connection>& conn, bool fromServer, const uint8_t* frame, size_t size) {
            if (size < 8)
                return;
            const uint32_t         object  = word(frame);
            const uint16_t         opcode  = static_cast<uint16_t>(word(frame + 4));
            const uint8_t*         payload = frame + 8;
            const size_t           length  = size - 8;
            std::vector<uintptr_t> invalidated;
            bool                   changed = false;
            auto&                  r       = registry();
            {
                std::scoped_lock lock(r.mutex);
                if (!conn->alive.load())
                    return;
                if (fromServer) {
                    if (object == 1 && opcode == 1 && length >= 4) { // wl_display.delete_id
                        const uint32_t deleted = word(payload);
                        const auto     it      = conn->keyboards.find(deleted);
                        if (it != conn->keyboards.end()) {
                            invalidated.push_back(it->second.token);
                            conn->keyboards.erase(it);
                            changed = true;
                        }
                        conn->objects.erase(deleted);
                        if (r.lastInput == conn.get() && r.lastInputKeyboard == deleted)
                            r.lastInput = nullptr;
                    } else if (conn->objects.contains(object) && conn->objects[object] == Object::Registry && opcode == 0 && length >= 12) {
                        // wl_registry.global(name, interface, version)
                        std::string_view interface;
                        size_t           end = 0;
                        if (getText(payload, length, 4, interface, end) && end + 4 <= length && interface == "wl_seat")
                            conn->seatGlobals.insert(word(payload));
                    } else if (conn->objects.contains(object) && conn->objects[object] == Object::Keyboard) {
                        auto it = conn->keyboards.find(object);
                        if (it == conn->keyboards.end())
                            return;
                        Keyboard& keyboard = it->second;
                        if (opcode == 1 && length >= 12) { // wl_keyboard.enter
                            invalidated.push_back(keyboard.token);
                            keyboard.focused = true;
                            keyboard.serial  = word(payload);
                            keyboard.surface = word(payload + 4);
                            keyboard.token   = ++r.nextToken;
                            if (!keyboard.token)
                                keyboard.token = ++r.nextToken;
                            r.lastInput = nullptr;
                            changed     = true;
                        } else if (opcode == 2 && length >= 8) { // wl_keyboard.leave
                            invalidated.push_back(keyboard.token);
                            keyboard.focused = false;
                            keyboard.surface = 0;
                            keyboard.token   = 0;
                            if (r.lastInput == conn.get() && r.lastInputKeyboard == object)
                                r.lastInput = nullptr;
                            changed = true;
                        } else if (opcode == 3 && length >= 16) { // wl_keyboard.key
                            keyboard.serial = word(payload);
                            keyboard.time   = word(payload + 4);
                            if (word(payload + 12) == 1 && keyboard.focused) {
                                r.lastInput         = conn.get();
                                r.lastInputKeyboard = object;
                            }
                        } else if (opcode == 4 && length >= 20) { // wl_keyboard.modifiers
                            keyboard.serial    = word(payload);
                            keyboard.depressed = word(payload + 4);
                            keyboard.latched   = word(payload + 8);
                            keyboard.locked    = word(payload + 12);
                            keyboard.group     = word(payload + 16);
                        }
                    }
                } else {
                    if (object == 1 && opcode == 1 && length >= 4) { // wl_display.get_registry(new_id)
                        conn->objects[word(payload)] = Object::Registry;
                    } else if (conn->objects.contains(object) && conn->objects[object] == Object::Registry && opcode == 0 && length >= 16) {
                        // wl_registry.bind(name, interface, version, new_id)
                        std::string_view interface;
                        size_t           end = 0;
                        if (getText(payload, length, 4, interface, end) && end + 8 <= length && interface == "wl_seat" && conn->seatGlobals.contains(word(payload))) {
                            conn->objects[word(payload + end + 4)] = Object::Seat;
                        }
                    } else if (conn->objects.contains(object) && conn->objects[object] == Object::Seat && opcode == 1 && length >= 4) {
                        // wl_seat.get_keyboard(new_id)
                        const uint32_t id = word(payload);
                        conn->objects[id] = Object::Keyboard;
                        conn->keyboards.emplace(id, Keyboard{});
                        changed = true;
                    } else if (conn->objects.contains(object) && conn->objects[object] == Object::Keyboard && opcode == 0) {
                        // wl_keyboard.release (since v3)
                        auto it = conn->keyboards.find(object);
                        if (it != conn->keyboards.end()) {
                            invalidated.push_back(it->second.token);
                            conn->keyboards.erase(it);
                            changed = true;
                        }
                        conn->objects.erase(object);
                        if (r.lastInput == conn.get() && r.lastInputKeyboard == object)
                            r.lastInput = nullptr;
                    }
                }
            }
            for (auto token : invalidated)
                cancelFocus(conn.get(), token);
            if (changed)
                updateReadiness();
        }

        struct Framer {
            std::vector<uint8_t> buffered;
            bool                 valid = true;
            bool                 aligned() const {
                return valid && buffered.empty();
            }

            void feed(const std::shared_ptr<Connection>& conn, bool fromServer, const uint8_t* data, size_t size) {
                if (!valid)
                    return;
                // Retain at most one incomplete frame, bounded by Wayland's 16-bit size.
                while (size) {
                    if (buffered.empty() && size >= 8) {
                        const uint32_t header = word(data + 4);
                        const size_t   length = header >> 16;
                        if (length < 8 || length > kMaxWireMessage || (length % 4) != 0) {
                            valid = false;
                            break;
                        }
                        if (length <= size) {
                            observe(conn, fromServer, data, length);
                            data += length;
                            size -= length;
                            continue;
                        }
                    }
                    if (buffered.size() < 8) {
                        const size_t n = std::min(size, 8 - buffered.size());
                        buffered.insert(buffered.end(), data, data + n);
                        data += n;
                        size -= n;
                        if (buffered.size() < 8)
                            continue;
                    }
                    const size_t length = word(buffered.data() + 4) >> 16;
                    if (length < 8 || length > kMaxWireMessage || (length % 4) != 0) {
                        valid = false;
                        break;
                    }
                    const size_t n = std::min(size, length - buffered.size());
                    buffered.insert(buffered.end(), data, data + n);
                    data += n;
                    size -= n;
                    if (buffered.size() == length) {
                        observe(conn, fromServer, buffered.data(), buffered.size());
                        buffered.clear();
                    }
                }
                if (!valid) {
                    // Malformed/unknown wire framing disables injection, not transport.
                    buffered.clear();
                    auto& r = registry();
                    {
                        std::scoped_lock lock(r.mutex);
                        conn->keyboards.clear();
                        conn->objects.clear();
                    }
                    updateReadiness();
                }
            }
        };

        // Keep the application's open-file-description flags untouched. Wait
        // for writable readiness instead of making forwarded sends blocking.
        bool waitWritable(int fd) {
            for (;;) {
                pollfd    pfd{fd, POLLOUT, 0};
                const int result = poll(&pfd, 1, -1);
                if (result < 0 && errno == EINTR)
                    continue;
                return result > 0 && (pfd.revents & POLLOUT) && !(pfd.revents & (POLLERR | POLLNVAL));
            }
        }

        bool sendAll(int fd, const uint8_t* data, size_t size) {
            while (size) {
                const ssize_t n = send(fd, data, size, MSG_NOSIGNAL | MSG_DONTWAIT);
                if (n < 0 && errno == EINTR)
                    continue;
                if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
                    if (!waitWritable(fd))
                        return false;
                    continue;
                }
                if (n <= 0)
                    return false;
                data += n;
                size -= static_cast<size_t>(n);
            }
            return true;
        }

        bool wireEvent(const Connection& conn, uint32_t keyboard, uint16_t opcode, const uint32_t* args, size_t count) {
            std::array<uint8_t, 8 + 5 * 4> frame{};
            if (count > 5)
                return false;
            const size_t size = 8 + count * 4;
            putWord(frame.data(), keyboard);
            putWord(frame.data() + 4, static_cast<uint32_t>((size << 16) | opcode));
            for (size_t i = 0; i < count; ++i)
                putWord(frame.data() + 8 + i * 4, args[i]);
            return sendAll(conn.relay, frame.data(), size);
        }

        // When the compositor sends an isolated wl_keyboard.keymap event with its
        // SCM_RIGHTS FD, obtain the real XKB modifier indices without linking to
        // libwayland-client or introducing a required xkbcommon dependency.
        void observeKeymapFd(const std::shared_ptr<Connection>& conn, const uint8_t* frame, size_t length, int fd) {
            if (length != 16 || fd < 0 || (word(frame + 4) & 0xffffU) != 0 || word(frame + 8) != 1)
                return;
            const uint32_t id      = word(frame);
            const uint32_t mapSize = word(frame + 12);
            if (mapSize == 0 || mapSize > (1U << 20))
                return;
            {
                auto&            r = registry();
                std::scoped_lock lock(r.mutex);
                if (!conn->keyboards.contains(id))
                    return;
            }
            void* mapping = mmap(nullptr, mapSize, PROT_READ, MAP_PRIVATE, fd, 0);
            if (mapping == MAP_FAILED)
                return;
            // The explicit trailing NUL also handles non-terminated compositor blobs.
            std::string keymap(static_cast<const char*>(mapping), mapSize);
            munmap(mapping, mapSize);
            keymap.push_back('\0');
            void* library = dlopen("libxkbcommon.so.0", RTLD_NOW | RTLD_LOCAL);
            if (!library)
                return;
            using NewContext  = void* (*)(int);
            using NewKeymap   = void* (*)(void*, const char*, int, int);
            using GetIndex    = uint32_t (*)(void*, const char*);
            using Unref       = void (*)(void*);
            auto contextNew   = reinterpret_cast<NewContext>(dlsym(library, "xkb_context_new"));
            auto keymapNew    = reinterpret_cast<NewKeymap>(dlsym(library, "xkb_keymap_new_from_string"));
            auto getIndex     = reinterpret_cast<GetIndex>(dlsym(library, "xkb_keymap_mod_get_index"));
            auto keymapUnref  = reinterpret_cast<Unref>(dlsym(library, "xkb_keymap_unref"));
            auto contextUnref = reinterpret_cast<Unref>(dlsym(library, "xkb_context_unref"));
            if (contextNew && keymapNew && getIndex && keymapUnref && contextUnref) {
                void* context = contextNew(0);
                if (context) {
                    void* xkb = keymapNew(context, keymap.c_str(), 1, 0);
                    if (xkb) {
                        auto&            r = registry();
                        std::scoped_lock lock(r.mutex);
                        auto             it = conn->keyboards.find(id);
                        if (it != conn->keyboards.end()) {
                            it->second.shiftIndex = getIndex(xkb, "Shift");
                            it->second.ctrlIndex  = getIndex(xkb, "Control");
                            it->second.altIndex   = getIndex(xkb, "Mod1");
                            it->second.superIndex = getIndex(xkb, "Mod4");
                        }
                        keymapUnref(xkb);
                    }
                    contextUnref(context);
                }
            }
            dlclose(library);
        }

        bool sameFocus(const Connection* conn, uint32_t keyboard, uintptr_t token) {
            auto&            r = registry();
            std::scoped_lock lock(r.mutex);
            if (!conn->alive.load())
                return false;
            const auto it = conn->keyboards.find(keyboard);
            return it != conn->keyboards.end() && it->second.focused && it->second.surface && it->second.token == token;
        }

        uint32_t modifierMask(const Keyboard& keyboard, uint32_t modifiers) {
            uint32_t mask = 0;
            if ((modifiers & kModifierShift) && keyboard.shiftIndex < 32)
                mask |= 1U << keyboard.shiftIndex;
            if ((modifiers & kModifierCtrl) && keyboard.ctrlIndex < 32)
                mask |= 1U << keyboard.ctrlIndex;
            if ((modifiers & kModifierAlt) && keyboard.altIndex < 32)
                mask |= 1U << keyboard.altIndex;
            if ((modifiers & kModifierSuper) && keyboard.superIndex < 32)
                mask |= 1U << keyboard.superIndex;
            return mask;
        }

        bool emitModifiers(const Connection& conn, uint32_t id, const Keyboard& keyboard, uint32_t depressed) {
            const uint32_t data[] = {keyboard.serial, depressed, keyboard.latched, keyboard.locked, keyboard.group};
            return wireEvent(conn, id, 4, data, 5);
        }

        void pump(const std::shared_ptr<Connection>& conn, const Framer& serverFrames) {
            if (!serverFrames.aligned())
                return; // Never inject halfway through a native wire message.
            pollfd pending{conn->upstream, POLLIN, 0};
            if (poll(&pending, 1, 0) > 0 && (pending.revents & POLLIN))
                return; // Forward queued compositor events before synthetic input.
            for (;;) {
                uint32_t  id    = 0;
                uintptr_t token = 0;
                Keyboard  state{};
                {
                    auto&            r = registry();
                    std::scoped_lock lock(r.mutex);
                    const auto       choice = focusLocked(r).candidate;
                    if (choice.count != 1 || choice.target.connection != conn.get())
                        return;
                    token = choice.target.focused;
                    for (const auto& [candidateId, candidate] : conn->keyboards) {
                        if (candidate.focused && candidate.token == token) {
                            id    = candidateId;
                            state = candidate;
                            break;
                        }
                    }
                }
                if (!id)
                    return;
                auto task = takeTask(HookBackend::Wayland, conn.get(), token);
                if (!task)
                    return;

                int         status = 0;
                KeySequence sequence(task->ops);
                while (const auto* op = sequence.operation()) {
                    if (!sameFocus(conn.get(), id, token) || (task->cancelled.load() && !sequence.needsRelease())) {
                        status = -ECANCELED;
                        break;
                    }
                    const uint32_t desired  = modifierMask(state, op->modifiers);
                    const uint32_t original = state.depressed;
                    if (desired != original && !emitModifiers(*conn, id, state, desired)) {
                        status = -EIO;
                        break;
                    }
                    while (sequence.operation() == op) {
                        if ((!sameFocus(conn.get(), id, token) || task->cancelled.load()) && !sequence.needsRelease()) {
                            status = -ECANCELED;
                            break;
                        }
                        const auto     edge   = sequence.current();
                        const uint32_t args[] = {state.serial, ++state.time, edge->keycode, edge->pressed ? 1U : 0U};
                        if (!wireEvent(*conn, id, 3, args, 4)) {
                            status = -EIO;
                            break;
                        }
                        if (edge->pressed)
                            task->applied.store(true, std::memory_order_release);
                        sequence.advance();
                    }
                    if (desired != original && sameFocus(conn.get(), id, token)) {
                        // Restore the latest real compositor modifier state.
                        Keyboard updated = state;
                        {
                            auto&            r = registry();
                            std::scoped_lock lock(r.mutex);
                            const auto       it = conn->keyboards.find(id);
                            if (it != conn->keyboards.end() && it->second.token == token)
                                updated = it->second;
                        }
                        if (!emitModifiers(*conn, id, updated, updated.depressed) && status == 0)
                            status = -EIO;
                    }
                    if (status != 0)
                        break;
                }
                {
                    auto&            r = registry();
                    std::scoped_lock lock(r.mutex);
                    const auto       it = conn->keyboards.find(id);
                    if (it != conn->keyboards.end() && it->second.token == token)
                        it->second.time = std::max(it->second.time, state.time);
                }
                if (status == 0 && !sameFocus(conn.get(), id, token))
                    status = -ECANCELED;
                std::scoped_lock lock(runtime().mutex);
                finishLocked(task, status);
            }
        }

        // Relay each recvmsg chunk with its ancillary data at the same stream offset.
        // Do not split messages or steal compositor-owned FDs from the application.
        struct Received {
            std::array<uint8_t, kReadChunk> data{};
            alignas(cmsghdr) std::array<char, CMSG_SPACE(kFdBudget * sizeof(int))> control{};
            ssize_t size        = 0;
            size_t  controlSize = 0;
            int     flags       = 0;
        };

        bool receive(int fd, Received& out) {
            iovec  iov{out.data.data(), out.data.size()};
            msghdr msg{};
            msg.msg_iov        = &iov;
            msg.msg_iovlen     = 1;
            msg.msg_control    = out.control.data();
            msg.msg_controllen = out.control.size();
            out.size           = recvmsg(fd, &msg, MSG_CMSG_CLOEXEC);
            out.controlSize    = msg.msg_controllen;
            out.flags          = msg.msg_flags;
            return out.size > 0;
        }

        void closeReceivedFds(Received& message) {
            msghdr msg{};
            msg.msg_control    = message.control.data();
            msg.msg_controllen = message.controlSize;
            for (cmsghdr* cmsg = CMSG_FIRSTHDR(&msg); cmsg; cmsg = CMSG_NXTHDR(&msg, cmsg)) {
                if (cmsg->cmsg_level != SOL_SOCKET || cmsg->cmsg_type != SCM_RIGHTS)
                    continue;
                const size_t n   = (cmsg->cmsg_len - CMSG_LEN(0)) / sizeof(int);
                const auto*  fds = reinterpret_cast<const int*>(CMSG_DATA(cmsg));
                for (size_t i = 0; i < n; ++i)
                    close(fds[i]);
            }
        }

        bool forward(int destination, Received& message) {
            if (message.flags & MSG_CTRUNC)
                return false;
            iovec  iov{message.data.data(), static_cast<size_t>(message.size)};
            msghdr msg{};
            msg.msg_iov        = &iov;
            msg.msg_iovlen     = 1;
            msg.msg_control    = message.controlSize ? message.control.data() : nullptr;
            msg.msg_controllen = message.controlSize;
            // SCM_RIGHTS belongs to the first successfully transmitted byte.
            // Retry sendmsg only while no bytes were transferred.
            ssize_t sent;
            for (;;) {
                sent = sendmsg(destination, &msg, MSG_NOSIGNAL | MSG_DONTWAIT);
                if (sent < 0 && errno == EINTR)
                    continue;
                if (sent < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
                    if (!waitWritable(destination))
                        return false;
                    continue;
                }
                break;
            }
            if (sent <= 0)
                return false;
            return sendAll(destination, message.data.data() + sent, message.size - sent);
        }

        void retire(const std::shared_ptr<Connection>& conn, bool broken) {
            if (broken) {
                shutdown(conn->upstream, SHUT_RDWR);
                shutdown(conn->relay, SHUT_RDWR);
            }
            if (conn->alive.exchange(false)) {
                auto&                  r = registry();
                std::vector<uintptr_t> invalidated;
                {
                    std::scoped_lock lock(r.mutex);
                    for (const auto& [id, key] : conn->keyboards) {
                        (void)id;
                        invalidated.push_back(key.token);
                    }
                    conn->keyboards.clear();
                    if (r.lastInput == conn.get())
                        r.lastInput = nullptr;
                }
                for (auto token : invalidated)
                    cancelFocus(conn.get(), token);
                updateReadiness();
            }
            if (conn->threads.fetch_sub(1) == 1) {
                auto&            r = registry();
                std::scoped_lock lock(r.mutex);
                auto             it = std::find(r.connections.begin(), r.connections.end(), conn);
                if (it != r.connections.end())
                    r.connections.erase(it);
            }
        }

        void relayThread(std::shared_ptr<Connection> conn, bool fromServer) {
            {
                std::unique_lock lock(conn->startMutex);
                conn->startCv.wait(lock, [&] { return conn->started || conn->abort; });
                if (conn->abort)
                    return;
            }
            const int source      = fromServer ? conn->upstream : conn->relay;
            const int destination = fromServer ? conn->relay : conn->upstream;
            Framer    frames;
            bool      cleanEof = false;
            try {
                for (;;) {
                    pollfd    fds[2] = {{source, POLLIN, 0}, {fromServer ? conn->notify : -1, POLLIN, 0}};
                    const int ready  = poll(fds, fromServer ? 2 : 1, -1);
                    if (ready < 0 && errno == EINTR)
                        continue;
                    if (ready <= 0)
                        break;
                    if (fds[0].revents & (POLLIN | POLLHUP)) {
                        Received   message;
                        const bool readOk = receive(source, message);
                        if (readOk) {
                            // Only parse keymap FD if one recvmsg contains exactly one
                            // complete keyboard.keymap frame and exactly one SCM_RIGHTS FD.
                            // Ambiguous mixed-FD batches are passed through unchanged.
                            if (fromServer && frames.aligned() && message.size >= 16 && static_cast<size_t>(message.size) == (word(message.data.data() + 4) >> 16)) {
                                msghdr fdmsg{};
                                fdmsg.msg_control    = message.control.data();
                                fdmsg.msg_controllen = message.controlSize;
                                int    singleFd      = -1;
                                size_t count         = 0;
                                for (cmsghdr* cmsg = CMSG_FIRSTHDR(&fdmsg); cmsg; cmsg = CMSG_NXTHDR(&fdmsg, cmsg)) {
                                    if (cmsg->cmsg_level != SOL_SOCKET || cmsg->cmsg_type != SCM_RIGHTS)
                                        continue;
                                    const size_t n = (cmsg->cmsg_len - CMSG_LEN(0)) / sizeof(int);
                                    count += n;
                                    if (n)
                                        singleFd = reinterpret_cast<int*>(CMSG_DATA(cmsg))[0];
                                }
                                if (count == 1)
                                    observeKeymapFd(conn, message.data.data(), message.size, singleFd);
                            }
                            frames.feed(conn, fromServer, message.data.data(), message.size);
                            const bool forwarded = forward(destination, message);
                            closeReceivedFds(message);
                            if (!forwarded)
                                break;
                            if (fromServer)
                                pump(conn, frames);
                        } else {
                            closeReceivedFds(message);
                            if (message.size < 0 && (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK))
                                continue;
                            cleanEof = message.size == 0;
                            break;
                        }
                    }
                    if (fromServer && (fds[1].revents & POLLIN)) {
                        uint64_t value;
                        while (read(conn->notify, &value, sizeof(value)) < 0 && errno == EINTR) {}
                        pump(conn, frames);
                    }
                    if (fds[0].revents & (POLLERR | POLLNVAL))
                        break;
                }
            } catch (...) {
                // A preload library must not terminate the host process on a backend
                // allocation/parser error. Disable this intercepted connection instead.
                cleanEof = false;
            }
            if (cleanEof)
                shutdown(destination, SHUT_WR); // Preserve a final opposite-direction reply.
            retire(conn, !cleanEof);
        }

        bool activate(int fd) {
            const int descriptorFlags = fcntl(fd, F_GETFD);
            const int statusFlags     = fcntl(fd, F_GETFL);
            if (descriptorFlags < 0 || statusFlags < 0)
                return false;
            int       socketType = 0;
            socklen_t typeSize   = sizeof(socketType);
            if (getsockopt(fd, SOL_SOCKET, SO_TYPE, &socketType, &typeSize) != 0 || socketType != SOCK_STREAM)
                return false;
            int pair[2];
            if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, pair) != 0)
                return false;
            const int upstream = fcntl(fd, F_DUPFD_CLOEXEC, 0);
            const int notify   = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
            if (upstream < 0 || notify < 0) {
                if (upstream >= 0)
                    close(upstream);
                if (notify >= 0)
                    close(notify);
                close(pair[0]);
                close(pair[1]);
                return false;
            }
            std::shared_ptr<Connection> conn;
            Registry*                   r = nullptr;
            try {
                conn = std::make_shared<Connection>();
                r    = &registry();
                ensureRuntimeInitialized();
            } catch (...) {
                close(upstream);
                close(notify);
                close(pair[0]);
                close(pair[1]);
                return false;
            }
            conn->upstream = upstream;
            conn->relay    = pair[1];
            conn->notify   = notify;

            std::thread downstream, upstreamThread;
            bool        registered = false;
            auto        abort      = [&] {
                {
                    std::scoped_lock lock(conn->startMutex);
                    conn->abort = true;
                }
                conn->startCv.notify_all();
                if (downstream.joinable())
                    downstream.join();
                if (upstreamThread.joinable())
                    upstreamThread.join();
                if (registered) {
                    std::scoped_lock lock(r->mutex);
                    auto             it = std::find(r->connections.begin(), r->connections.end(), conn);
                    if (it != r->connections.end())
                        r->connections.erase(it);
                }
                close(pair[0]);
            };
            try {
                downstream     = std::thread(relayThread, conn, true);
                upstreamThread = std::thread(relayThread, conn, false);
                {
                    std::scoped_lock lock(r->mutex);
                    r->connections.push_back(conn);
                    registered = true;
                }
            } catch (...) {
                abort();
                return false;
            }
            if (dup2(pair[0], fd) < 0) {
                abort();
                return false;
            }
            close(pair[0]);
            // The application keeps its original nonblocking and close-on-exec flags.
            (void)fcntl(fd, F_SETFD, descriptorFlags);
            (void)fcntl(fd, F_SETFL, statusFlags);
            // Keep upstream flags unchanged; forwarding retries EAGAIN itself.
            downstream.detach();
            upstreamThread.detach();
            {
                std::scoped_lock lock(conn->startMutex);
                conn->started = true;
            }
            conn->startCv.notify_all();
            return true;
        }

    } // namespace

    // The existing IPC worker is compiled into this library, with only the wire
    // frontend linked. No X11/XCB/API-hook symbols are exported or installed.
    void            resetX11AfterFork() {}
    void            resetXcbAfterFork() {}
    void            resetWaylandAfterFork() {}
    void            wakeX11() {}
    void            wakeXcb() {}
    void            loadX11() {}
    void            loadXcb() {}
    void            loadWayland() {}
    FocusCandidates focusedX11Candidates() {
        return {};
    }
    FocusCandidates focusedXcbCandidates() {
        return {};
    }
    FocusCandidates focusedWaylandCandidates() {
        Registry* current = activeRegistry.load(std::memory_order_acquire);
        if (!current || current->pid != getpid())
            return {};
        std::scoped_lock lock(current->mutex);
        return focusLocked(*current).candidate;
    }
    void wakeWayland() {
        Registry* current = activeRegistry.load(std::memory_order_acquire);
        if (!current || current->pid != getpid())
            return;
        std::scoped_lock lock(current->mutex);
        for (const auto& conn : current->connections) {
            if (!conn->alive.load())
                continue;
            const uint64_t one = 1;
            (void)write(conn->notify, &one, sizeof(one));
        }
    }
} // namespace lotus::apphook

/** Only globally visible entrypoint in this library. */
extern "C" __attribute__((visibility("default"))) int connect(int fd, const sockaddr* address, socklen_t length) {
    // Respect other preload interposers' ordering. The direct syscall is only
    // a bootstrap fallback if the loader cannot resolve the next symbol.
    using Connect = int (*)(int, const sockaddr*, socklen_t);
    static std::atomic<Connect> nextConnect{nullptr};
    Connect                     next = nextConnect.load(std::memory_order_acquire);
    if (!next) {
        next = reinterpret_cast<Connect>(dlsym(RTLD_NEXT, "connect"));
        if (next == &connect)
            next = nullptr;
        if (next)
            nextConnect.store(next, std::memory_order_release);
    }
    const int result = next ? next(fd, address, length) : static_cast<int>(syscall(SYS_connect, fd, address, length));
    if (result != 0)
        return result;
    if (!lotus::apphook::isWaylandSocket(address, length))
        return result;
    const int savedErrno = errno;
    try {
        (void)lotus::apphook::activate(fd); // Best effort; failure leaves native socket connected.
    } catch (...) {
        // Do not propagate C++ exceptions across libc's connect() boundary.
    }
    errno = savedErrno;
    return result;
}
