#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub enum Pairy<X,Y,Z> { Two(X,Y), One(Z), None }

pub fn foo<A,B:Copy>(c: || -> Pairy<(A,A),bool,B>,
                     dA: |A| -> i8,
                     dB: |B| -> i8) -> i8 {
    let s = c();
    let ret = match s {
        Two((a1,a2), _) => dA(a1) + dA(a2),
        One(b) => dB(b),
        None => 5,
    };
    c();
    ret
}
