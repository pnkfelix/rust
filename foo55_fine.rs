#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

// reduced version of foo51.rs
#[lang="sized"] pub trait Sized { }

#[lang="quiet_early_drop"]
pub trait QuietEarlyDrop { }


pub struct Vec<T> {
    _len: uint,
    _cap: uint,
    _ptr: *mut T
}

impl<T:QuietEarlyDrop> QuietEarlyDrop for Vec<T> {}

pub struct String {
    _vec: Vec<u8>,
}

pub fn foo<T>(b: || -> bool, f: || -> String, g: || -> T) -> T {
    let ret = if b() {
        let _s = f();
        g()
    } else {
        g()
    };
    f();
    ret
}
