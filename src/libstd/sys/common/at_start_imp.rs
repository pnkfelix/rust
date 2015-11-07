// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use boxed::Box;
use ptr;
use sys_common::mutex::Mutex;
use vec::Vec;

type Queue = Vec<Box<Fn()>>;

// NB these are specifically not types from `std::sync` as they currently rely
// on poisoning and this module needs to operate at a lower level than requiring
// the thread infrastructure to be in place (useful on the borders of
// initialization/destruction).
static LOCK: Mutex = Mutex::new();
static mut QUEUE: *mut Queue = ptr::null_mut();

unsafe fn init() -> bool {
    if QUEUE.is_null() {
        let state: Box<Queue> = box Vec::new();
        QUEUE = Box::into_raw(state);
    }

    true
}

/// Runs every procedure enqueued at the time that this was invoked.
/// (recursively-enqueued procedures will not be run by this
/// invocation).
pub fn run_all() {
    let enqueued: Vec<_>;
    unsafe {
        LOCK.lock();
        let queue = QUEUE;
        if queue as usize != 0 {
            enqueued = (*queue).iter().collect();
            LOCK.unlock();
        } else {
            LOCK.unlock();
            return;
        }
    }

    for ref to_run in &enqueued {
        to_run();
    }
}

/// Pushes `f` onto the queue of procedures to invoke on each thread,
/// from the context of that thread, when it starts executing.
pub fn push(f: Box<Fn()>) -> bool {
    let mut ret = true;
    unsafe {
        LOCK.lock();
        if init() {
            (*QUEUE).push(f);
        } else {
            ret = false;
        }
        LOCK.unlock();
    }
    ret
}
