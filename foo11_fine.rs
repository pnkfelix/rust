#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub enum Foo<A,B> { Fx(A), Fy(B) }

pub fn foo<X,Y>(c: || -> Foo<X,Y>, f: |X| -> int, g: |Y| -> int) -> int {
    let s = c();
    //                                                          // NEEDS_DROP={s}
    let ret = match s {
        Fx(x) => {
    //                                                          // NEEDS_DROP={x}
            f(x)
    //                                                          // NEEDS_DROP={}
        }
        Fy(y) => {
    //                                                          // NEEDS_DROP={y}
            g(y)
    //                                                          // NEEDS_DROP={}
        }
    }; // ... this should be fine.
    c();
    ret
}
