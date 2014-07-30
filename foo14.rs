#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub enum Foo<A> { Fx(A) }

pub fn foo<X>(s: Foo<X>, f: |X| -> int) -> int {
    //                                                          // NEEDS_DROP={s}
    match s {
        Fx(x) => {
    //                                                          // NEEDS_DROP={x}
            f(x)
    //                                                          // NEEDS_DROP={}
        }
    } // ... this should be fine.
}
