#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }
#[lang="send"]  pub trait Send { }


/// A type that represents a uniquely-owned value.
#[lang = "owned_box"]
pub struct Box<T>(*mut T);

pub fn foo<T>(b: bool, c: || -> Box<T>, f: |Box<T>| -> int) -> int {
    let x = c();
    //                                                          // NEEDS_DROP={x}
    let ret = if b {
    //                                                          // NEEDS_DROP={x}
        f(x) // Variable x copied in this branch ...
    //                                                          // NEEDS_DROP={}
    } else {
    //                                                          // NEEDS_DROP={x}
        3    // ... but not this one ...
    //                                                          // NEEDS_DROP={x}
    }; // ... thus expect notice at this join-point.
    //                                                          // NEEDS_DROP={}
    c();
    ret
}
