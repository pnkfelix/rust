#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn drop<T>(_x: T) { }

pub enum Foo<A,B> { Fx(A), Fy(B) }

pub fn foo<X,Y:Copy>(c: || -> Foo<X,Y>, f: |X| -> int, f2: |&X| -> int, g: |Y| -> int) -> int {
    let s = c();
    //                                                          // NEEDS_DROP={s}
    let ret = match s {
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
    }; // ... at some point, I wrote here "this should be fine"
    // but I no longer understand why I thought that, since there
    // are true mismatches in the drop obligations for the left and right hand
    // sides above.
    c();
    ret
}
