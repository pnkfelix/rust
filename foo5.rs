#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub struct Foo<X,Y> { _x: X, _y: Y, _z: X }

pub fn foo<X,Y:Copy>(b: bool, s: Foo<X,Y>, f: |X| -> int) -> int {
    //                                                          // NEEDS_DROP={s}
    if b {
        //                                                      // NEEDS_DROP={s}
        f(s._x) // Path s._x moved in this branch ...
        //                                                      // NEEDS_DROP={s._z}
    } else {
        //                                                      // NEEDS_DROP={s}
        3    // ... but not this one ...
        //                                                      // NEEDS_DROP={s}
    } // ... thus expect notice at this join-point.
}
