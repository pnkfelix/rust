#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn foo<X>(c: || -> (X,u8), f: |X| -> i8) -> i8 {
    let s = c();
    //                                                          // NEEDS_DROP={s}
    let ret = match s {
        (b, 0) |
        (b, 1) => {
            //                                                  // NEEDS_DROP={b}
            f(b) + 2
                //                                              // NEEDS_DROP={}
        }
        (b, _) => {
            //                                                  // NEEDS_DROP={b}
            f(b) + 3
            //                                                  // NEEDS_DROP={}
        }
    }; // ... this should be fine.
    c();
    ret
}
