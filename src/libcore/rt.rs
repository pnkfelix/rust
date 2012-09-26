// NB: transitionary, de-mode-ing.
#[forbid(deprecated_mode)];
#[forbid(deprecated_pattern)];
//! Runtime calls emitted by the compiler.

use libc::c_char;
use libc::c_void;
use libc::size_t;
use libc::uintptr_t;

use gc::{cleanup_stack_for_failure, gc, Word};
use memory_watcher;

#[allow(non_camel_case_types)]
type rust_task = c_void;

extern mod rustrt {
    #[legacy_exports];
    #[rust_stack]
    fn rust_upcall_fail(expr: *c_char, file: *c_char, line: size_t);

    #[rust_stack]
    fn rust_upcall_exchange_malloc(td: *c_char, size: uintptr_t) -> *c_char;

    #[rust_stack]
    fn rust_upcall_exchange_free(ptr: *c_char);

    #[rust_stack]
    fn rust_upcall_malloc(td: *c_char, size: uintptr_t) -> *c_char;

    #[rust_stack]
    fn rust_upcall_free(ptr: *c_char);

    fn rust_global_memory_watcher_chan_ptr() -> *uintptr_t;
}

// FIXME (#2861): This needs both the attribute, and the name prefixed with
// 'rt_', otherwise the compiler won't find it. To fix this, see
// gather_rust_rtcalls.
#[rt(fail_)]
fn rt_fail_(expr: *c_char, file: *c_char, line: size_t) {
    cleanup_stack_for_failure();
    rustrt::rust_upcall_fail(expr, file, line);
}

#[rt(exchange_malloc)]
fn rt_exchange_malloc(td: *c_char, size: uintptr_t) -> *c_char {
    return rustrt::rust_upcall_exchange_malloc(td, size);
}

// NB: Calls to free CANNOT be allowed to fail, as throwing an exception from
// inside a landing pad may corrupt the state of the exception handler. If a
// problem occurs, call exit instead.
#[rt(exchange_free)]
fn rt_exchange_free(ptr: *c_char) {
    rustrt::rust_upcall_exchange_free(ptr);
}

#[rt(malloc)]
fn rt_malloc(td: *c_char, size: uintptr_t) -> *c_char {
    
    let memory_watcher_initialized = rustrt::rust_global_memory_watcher_chan_ptr();
    unsafe {
    	if(*memory_watcher_initialized == 0) {
    	}
    	else {
		let comm_memory_watcher_chan = memory_watcher::get_memory_watcher_Chan();
		comm_memory_watcher_chan.send(memory_watcher::ReportAllocation(task::get_task(),size,td));
    	}
    }
    
    return rustrt::rust_upcall_malloc(td, size);
}

// NB: Calls to free CANNOT be allowed to fail, as throwing an exception from
// inside a landing pad may corrupt the state of the exception handler. If a
// problem occurs, call exit instead.
#[rt(free)]
fn rt_free(ptr: *c_char) {
    rustrt::rust_upcall_free(ptr);
}

// Local Variables:
// mode: rust;
// fill-column: 78;
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// End:
