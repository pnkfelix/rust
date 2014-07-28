#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub enum Option<T> { None, Some(T), }

pub fn foo<T>(x: Option<T>, optb: Option<T>) -> Option<T> {
    match x {
        // The use of `_` here means that this is a borrowing match of `x`...
        Some(_) => { drop(optb); x }

        // ... which means that `x` has not been dropped on this path
        // (*even though* we know that `x` is `None` and thus is not
        // needs-drop on this path) :(
        None => optb
    }
}
