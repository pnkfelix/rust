#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub struct Foo<X,Y> { _x: X, _y: Y, _z: X, _w: X }

pub fn foo<X,Y:Copy>(b: bool, mut s: Foo<X,Y>, f: |X| -> int) -> int {
    s._x = s._z; // s._x assigned here (and s._z moved here).
    if b {
        f(s._x) // Path s._x moved in this branch ...
    } else {
        3    // ... but not this one ...
    } // ... thus expect notice at this join-point.
}
