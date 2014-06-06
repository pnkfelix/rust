#![no_std]

#![crate_type="lib"]

#[lang="sized"] pub trait Sized { }

pub struct Par<T> { x: T, y: T }

pub fn f<T>(b1: T, b2: T) -> Par<T> {
    let p = Par { x: b1, y: b2 };
    Par { y: p.y, ..p }
}
