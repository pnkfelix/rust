#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="sized"] pub trait Sized { }

pub fn foo<T>(b: bool, x: T, f: |T| -> int) -> int {
    //                                                          // NEEDS_DROP={x}
    if b {
    //                                                          // NEEDS_DROP={x}
        f(x) // Variable x moved in this branch ...
    //                                                          // NEEDS_DROP={}
    } else {
    //                                                          // NEEDS_DROP={x}
        3    // ... but not this one ...
    //                                                          // NEEDS_DROP={x}
    } // ... thus expect notice at this join-point.
}
