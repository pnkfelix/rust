#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }
#[lang="send"]  pub trait Send { }


/// A type that represents a uniquely-owned value.
#[lang = "owned_box"]
pub struct Box<T>(*mut T);

pub struct Foo<X,Y> { _x: X, _y: Y }

pub fn foo<T>(b: bool, c: || -> Foo<Box<T>,T>, f: |Box<T>| -> int) -> int {
    let s = c();
    //                                                          // NEEDS_DROP={s}
    let ret = if b {
    //                                                          // NEEDS_DROP={s}
        f(s._x) // Path s._x moved in this branch ...
    //                                                          // NEEDS_DROP={s._y}
    } else {
    //                                                          // NEEDS_DROP={s}
        3    // ... but not this one ...
    //                                                          // NEEDS_DROP={s}
    }; // ... thus expect notice at this join-point.
    //                                                          // NEEDS_DROP={}
    c();
    ret
}
