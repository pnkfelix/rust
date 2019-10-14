#![no_std]
#![feature(unwind_attributes)]
#![crate_type="lib"]

extern crate std;

#[inline(never)]
#[cold]
pub fn expect_failed(msg: &str) -> ! {
    panic!("{}", msg)
}
