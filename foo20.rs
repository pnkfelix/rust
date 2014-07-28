#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn foo<X>(t: &(i8, X)) -> i8 {
    let &(a, _) = t;
    let &(b, _) = t;
    a + b
}
