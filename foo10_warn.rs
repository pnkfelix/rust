#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub struct Foo<X,Y> { _x: X, _y: Y, _z: X, _w: X }

pub fn foo<X,Y:Copy>(b: bool, c: || -> Foo<X,Y>, f: |X| -> int) -> int {
    let mut s = c();
    //                                                          // NEEDS_DROP={s}
    s._x = s._z; // s._x assigned here (and s._z moved here).
    //                                                          // NEEDS_DROP={s._x, s._w}
    let ret = if b {
        //                                                      // NEEDS_DROP={s._x, s._w}
        f(s._x) // Path s._x moved in this branch ...
        //                                                      // NEEDS_DROP={s._w}
    } else {
        //                                                      // NEEDS_DROP={s._x, s._w}
        3    // ... but not this one ...
        //                                                      // NEEDS_DROP={s._x, s._w}
    }; // ... thus expect notice at this join-point.
    c();
    ret
}
