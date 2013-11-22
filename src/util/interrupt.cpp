/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "util/exception.h"

namespace lean {
static thread_local std::atomic_bool g_interrupt;

void request_interrupt() {
    g_interrupt.store(true);
}

void reset_interrupt() {
    g_interrupt.store(false);
}

bool interrupt_requested() {
    return g_interrupt.load();
}

void check_interrupted() {
    if (interrupt_requested()) {
        reset_interrupt();
        throw interrupted();
    }
}

void sleep_for(unsigned ms, unsigned step_ms) {
    if (step_ms == 0)
        step_ms = 1;
    unsigned rounds = ms / step_ms;
    std::chrono::milliseconds c(step_ms);
    std::chrono::milliseconds r(ms % step_ms);
    for (unsigned i = 0; i < rounds; i++) {
        std::this_thread::sleep_for(c);
        check_interrupted();
    }
    std::this_thread::sleep_for(r);
}

std::atomic_bool * interruptible_thread::get_flag_addr() {
    return &g_interrupt;
}

bool interruptible_thread::interrupted() const {
    std::atomic_bool * f = m_flag_addr.load();
    if (f == nullptr)
        return false;
    return f->load();
}

void interruptible_thread::request_interrupt(unsigned try_ms) {
    while (true) {
        std::atomic_bool * f = m_flag_addr.load();
        if (f != nullptr) {
            f->store(true);
            return;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(try_ms));
        check_interrupted();
    }
}

void interruptible_thread::join() {
    m_thread.join();
}

bool interruptible_thread::joinable() {
    return m_thread.joinable();
}
}
