#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub fn foo<X>(b: || -> bool,
              c: || -> X,
              d: |X| -> i8) -> i8 {
    let mut count = d(c());
    while count > 0 {
        count -= 1;
        let s_loop = c();
        if b() {
            d(s_loop);
        }
    }

    let s_return = c();
    if b() {
        if b() {
            d(s_return)
        } else {
            3
        }
    } else {
        return if b() { // TODO: Stlll not handling this right
            d(s_return)
        } else {
            3
        };
    }
}
