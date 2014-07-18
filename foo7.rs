#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub struct Foo<X,Y> { _x: X, _y: Y, _z: X }

pub fn foo<X,Y:Copy>(b: bool, mut s: Foo<X,Y>, _f: |X| -> int, x: X) -> int {
    //                                                          // NEEDS_DROP={s,x}
    if b {
        //                                                      // NEEDS_DROP={s,x}
        s._x = x; // `x` moved in this branch
        //                                                      // NEEDS_DROP={s}
        4
    } else {
        //                                                      // NEEDS_DROP={s,x}
        3    // ... but not this one ...
        //                                                      // NEEDS_DROP={s,x}
    } // ... thus expect notice at this join-point.
}
