#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub enum Foo<A,B> { Fx(A), Fy(B) }

pub fn foo<X,Y:Copy>(s: Foo<X,Y>, f: |X| -> int, f2: |&X| -> int, g: |Y| -> int) -> int {
    //                                                          // NEEDS_DROP={s}
    match s {
        Fx(ref x2) if true => {
    //                                                          // NEEDS_DROP={s}
            f2(x2)
    //                                                          // NEEDS_DROP={s}
        }
        Fx(x) => {
    //                                                          // NEEDS_DROP={x}
            f(x)
    //                                                          // NEEDS_DROP={}
        }
        Fy(y) => {
    //                                                          // NEEDS_DROP={}
            g(y)
    //                                                          // NEEDS_DROP={}
        }
    } // ... this should be fine.
}
