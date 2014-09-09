#![feature(lang_items)]
#![no_std]
#![allow(dead_code)]
#![allow(unused_variable)]
#![allow(dead_assignment)]

#![crate_type="lib"]

#[lang="sized"] pub trait Sized { }
#[lang="drop"] pub trait Drop { fn drop(&mut self); }
pub enum Option<T> { None, Some(T), }

// (PRELUDE ENDS ABOVE)

pub enum Pairy<X> { Two(X,X), One(X,X) }
pub fn foo<A>(c: || -> Pairy<A>,
              dA: |A| -> i8,
              dR: |&A| -> i8) -> i8 {
    let s = c();
    let ret = match s {
        Two(ref r1, ref r2) => {
            dR(r1) + dR(r2)
        }
        One(a1, a2) => {
            dA(a1) + dA(a2)
        }
    };
    c();
    ret
}
