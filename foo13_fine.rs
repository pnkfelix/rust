#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub enum Foo<A,B> { Fx(A), Fy(B) }

pub fn foo<X,Y:Copy>(b: || -> bool,
                     c: || -> Foo<X,Y>,
                     f: |X| -> int,
                     g: |Y| -> int) -> int {
    let s = c();
    //                                                          // NEEDS_DROP={s}
    let ret = match s {
        Fx(_) if b() => {
    //                                                          // NEEDS_DROP={s}
            drop(s);
    //                                                          // NEEDS_DROP={}
            3
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
    }; // ... this should be fine"
    c();
    ret
}
