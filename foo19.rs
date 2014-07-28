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
        Two((a1,a2), true) => dA(a1) + dA(a2),

        Two((_,a2), false) => dA(a2),
                            // this is an example of `_` being an
                            // "autodrop", since user could not write
                            // the drop themselves except by binding
                            // it to name, which would be a misfeature
                            // in the language.

        One(b) => dB(b),
        None => 5,
    };
    c();
    ret
}
