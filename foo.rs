#![no_std]
#![crate_type="lib"]

#[lang="exchange_free"]
unsafe fn exchange_free(_ptr: *mut u8) { loop { } }

#[lang="sized"]
pub trait Sized {}

pub type GBT = proc(v: int) -> int;

pub fn with_wrap(_wrap: GBT) -> GBT
{
    proc(_body) { _wrap((_body)) }
}
