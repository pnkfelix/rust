#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub enum Ordering { Less = -1i, Equal = 0i, Greater = 1i, }

pub trait Ord {
    fn cmp(&self, _other: &Self) -> bool { loop { } }
}
impl Ord for int { }

pub fn foo(x: &int) -> int {
    match *x {
        n if n.cmp(&0) => 1,  // int is copy ...
        0              => 0,  // ... and that is all ...
        _              => -1, // ... we are looking at.
    } // So should be fine at this join point.
}
