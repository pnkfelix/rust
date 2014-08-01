#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn foo<T:Copy>(b: bool, c: || -> T, f: |T| -> int) -> int {
    let x = c();
    //                                                          // NEEDS_DROP={}
    let ret = if b {
    //                                                          // NEEDS_DROP={}
        f(x) // Variable x copied in this branch ...
    //                                                          // NEEDS_DROP={}
    } else {
    //                                                          // NEEDS_DROP={}
        3    // ... but not this one ...
    //                                                          // NEEDS_DROP={}
    }; // ... but since it is copy, needs-drop = {}.  (Copy and Drop are mutually exclusive)
    //                                                          // NEEDS_DROP={}
    c();
    ret
}
