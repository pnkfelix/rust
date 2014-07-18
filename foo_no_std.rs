#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="sized"] pub trait Sized { }

pub fn foo<T>(b: bool, x: T, f: |T| -> int) -> int {
    if b {
        f(x)
    } else {
        3
    }
}
