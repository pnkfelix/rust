#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn foo<T:Copy>(b: bool, x: T, f: |T| -> int) -> int {
    //                                                          // NEEDS_DROP={}
    if b {
    //                                                          // NEEDS_DROP={}
        f(x) // Variable x copied in this branch ...
    //                                                          // NEEDS_DROP={}
    } else {
    //                                                          // NEEDS_DROP={}
        3    // ... but not this one ...
    //                                                          // NEEDS_DROP={}
    } // ... but since it is copy, needs-drop = {}.  (Copy and Drop are mutually exclusive)
    //                                                          // NEEDS_DROP={}
}
