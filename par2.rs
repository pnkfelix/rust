#![no_std]

#![crate_type="lib"]

#[lang="sized"] pub trait Sized { }

pub struct Par<T> { x: T, y: T }

pub fn f<T>(b1: T, b2: T, b3: T, b4: T) -> Par<T> {
    let p = Par { x: b1, y: b2 };
    let q = Par { x: b3, y: b4 };

    let s = Par { y: q.y, ..p };
    let _t = Par { y: p.y, ..q };
    s
}
