#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub struct Foo<X,Y> { _x: X, _y: Y, _z: X }

pub fn foo<X,Y:Copy>(b: bool, c: || -> Foo<X,Y>, _f: |X| -> int, _g: || -> X) -> int {
    let mut s = c();
    //                                                          // NEEDS_DROP={s}
    _f(s._x);
    //                                                          // NEEDS_DROP={s._z}
    _f(s._z);
    //                                                          // NEEDS_DROP={}
    // all of `s` is moved away ...
    let ret = if b {
        //                                                      // NEEDS_DROP={}
        s._x = _g(); // but `s._x` is re-established in this branch
        //                                                      // NEEDS_DROP={s._x}
        4
    } else {
        //                                                      // NEEDS_DROP={}
        3 // ... but not this one ...
    }; // ... thus expect notice at this join-point.
    c();
    ret
}
