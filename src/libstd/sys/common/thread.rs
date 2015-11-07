// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use prelude::v1::*;

use alloc::boxed::FnBox;
use libc;
use sys::stack_overflow;
use super::at_start_imp;

/// A stack extent represents the area covered by the thread's stack.
///
/// A stack has a "hot end" where all the pushing/popping is currently
/// happening and a "cold end" that is the opposite side.  (The "cold
/// end" is sometimes called the "base" of the stack, though that is
/// also sometimes used to refer to the end with low-valued
/// addresses). The hot end changes frequently as the stack grows and
/// shrinks, but the cold end is constant (as long as the stack itself
/// is not replaced).
///
/// ```
/// cold end        hot end        guard
///    |               |             |
///
///    +-----------------------------+
///    |                             |
///    | stack grows ===>            |
///    |                             |
///    +-----------------------------+
/// ```
#[derive(Copy, Clone)]
pub struct Extent { pub cold_end: usize, pub guard: usize }

#[allow(dead_code)]
impl Extent {
    fn low_address_end(&self) -> usize { debug_assert!(self.guard < self.cold_end); self.guard }
    fn high_address_end(&self) -> usize { debug_assert!(self.guard < self.cold_end); self.cold_end }
    fn cold_end(&self) -> usize { self.cold_end }
    fn guard_end(&self) -> usize { self.guard }
}

pub unsafe fn start_thread(main: *mut libc::c_void) {
    // Next, set up our stack overflow handler which may get triggered if we run
    // out of stack.
    let _handler = stack_overflow::Handler::new();

    // Next, run all the registered thread_start procedures.
    at_start_imp::run_all();

    // Finally, let's run some code.
    Box::from_raw(main as *mut Box<FnBox()>)()
}
