#![no_std]
#![crate_type="lib"]

extern crate core;
extern crate alloc;

use alloc::owned::Box;
use core::ops::Drop;

struct S;
impl Drop for S { fn drop(&mut self) { } }

pub extern fn thread_start(f: Box<S>) {
    (*f);
    0;
}
