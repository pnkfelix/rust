#![no_std]

#![crate_type="lib"]

#[lang="sized"] pub trait Sized { }

pub fn f<T>(base: T, flag: bool) -> T {
    if flag { base }
    else {
        let acc = base;
        acc
    }
}
