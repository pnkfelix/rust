// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!

The task interface to the runtime

*/

#[doc(hidden)]; // FIXME #3538

use libc;
use sys::{Task, Closure};

#[allow(non_camel_case_types)] // runtime type
pub type sched_id = int;
#[allow(non_camel_case_types)] // runtime type
pub type task_id = int;

extern {
    #[rust_stack]
    fn rust_task_yield(task: *Task) -> bool;

    fn rust_get_sched_id() -> sched_id;
    fn rust_new_sched(num_threads: libc::uintptr_t) -> sched_id;
    fn rust_sched_threads() -> libc::size_t;
    fn rust_sched_current_nonlazy_threads() -> libc::size_t;
    fn rust_num_threads() -> libc::uintptr_t;

    fn get_task_id() -> task_id;
    #[rust_stack]
    fn rust_get_task() -> *Task;

    fn new_task() -> *Task;
    fn rust_new_task_in_sched(id: sched_id) -> *Task;

    fn start_task(task: *Task, closure: *Closure);

    fn rust_task_is_unwinding(task: *Task) -> bool;
    fn rust_osmain_sched_id() -> sched_id;
    #[rust_stack]
    fn rust_task_inhibit_kill(t: *Task);
    #[rust_stack]
    fn rust_task_allow_kill(t: *Task);
    #[rust_stack]
    fn rust_task_inhibit_yield(t: *Task);
    #[rust_stack]
    fn rust_task_allow_yield(t: *Task);
    fn rust_task_kill_other(task: *Task);
    fn rust_task_kill_all(task: *Task);

    #[rust_stack]
    fn rust_get_task_local_data(task: *Task) -> *libc::c_void;
    #[rust_stack]
    fn rust_set_task_local_data(task: *Task, map: *libc::c_void);
    #[rust_stack]
    fn rust_task_local_data_atexit(task: *Task, cleanup_fn: *u8);
}
