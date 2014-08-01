#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub struct Foo<X,Y> { _x: X, _y: Y }

pub fn foo<X,Y:Copy>(b: bool, c: || -> Foo<X,Y>, f: |X| -> int, _g: |Y| -> int) -> int {
    let s = c();
    //                                                          // NEEDS_DROP={s}
    let ret = if b {
    //                                                          // NEEDS_DROP={s}
        f(s._x) // Path s._x moved in this branch ...
    //                                                          // NEEDS_DROP={}
    } else {
    //                                                          // NEEDS_DROP={s}
        3    // ... but not this one ...
    //                                                          // NEEDS_DROP={s}
    }; // ... thus expect notice at this join-point.
    c();
    ret
}
