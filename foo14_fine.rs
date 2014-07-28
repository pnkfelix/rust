#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub enum Foo<A> { Fx(A) }

pub fn foo<X>(c: || -> Foo<X>, f: |X| -> int) -> int {
    let s = c();
    //                                                          // NEEDS_DROP={s}
    let ret = match s {
        Fx(x) => {
    //                                                          // NEEDS_DROP={x}
            f(x)
    //                                                          // NEEDS_DROP={}
        }
    }; // ... this should be fine.
    c();
    ret
}
