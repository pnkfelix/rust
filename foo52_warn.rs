#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

// reduced version of foo51.rs
#[lang="sized"] pub trait Sized { }

#[lang="quiet_early_drop"]
pub trait QuietEarlyDrop { }

pub fn foo<T>(b: || -> bool, f: || -> T) -> T {
    let result = f();

    let ret = if b() {
        result
    } else {
        f()
    };

    ret
}
