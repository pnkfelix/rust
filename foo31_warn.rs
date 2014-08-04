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

pub fn foo<T>(b: bool, c: || -> Foo<Box<Foo<T,T>>,T>, f: |T| -> int) -> int {
    let s = c();
    //                                                          // NEEDS_DROP={s}
    let ret = if b {
    //                                                          // NEEDS_DROP={s}
        f(s._x._y) // Path s._x._y consumed in this branch ...
    //                                                          // NEEDS_DROP={s._y, s._x._x}
    } else {
    //                                                          // NEEDS_DROP={s}
        f(s._y)    // ... but not this one ...
    //                                                          // NEEDS_DROP={s._x}
    }; // ... thus expect notice at this join-point.
    //                                                          // NEEDS_DROP={}
    c();
    ret
}
