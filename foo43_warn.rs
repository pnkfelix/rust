#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }
#[lang="drop"] pub trait Drop { fn drop(&mut self); }

pub struct Foo<X,Y> { _x: X, _y: Y }

#[quiet_early_drop]
pub struct S;

impl Drop for S { fn drop(&mut self) { } }

#[warn(quiet_early_drop)]
pub fn foo<Y:Copy>(b: bool, c: || -> Foo<S,Y>, f: |S| -> int, _g: |Y| -> int) -> int {
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
    }; // ... thus expect notice here (requested warn on quiet_early_drop)
    c();
    ret
}
