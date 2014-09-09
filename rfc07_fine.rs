#![feature(lang_items)]
#![no_std]
#![allow(dead_code)]
#![allow(unused_variable)]
#![allow(dead_assignment)]

#![crate_type="lib"]

#[lang="sized"] pub trait Sized { }
#[lang="drop"] pub trait Drop { fn drop(&mut self); }
pub enum Option<T> { None, Some(T), }

// (PRELUDE ENDS ABOVE)

pub struct D;
impl Drop for D { fn drop(&mut self) { } }

pub fn foo(b: || -> bool, c: || -> D, f: |D| -> i8) -> i8 {

    //                                      DROP OBLIGATIONS
    //                                  ------------------------
    //                                  {       }

    let x = c();
    //                                  {     x }
    let y = c();
    //                                  {     x, y }

    if b() {
        //                                  { x, y }
        let ret = f(x);
        //                                  {    y }
        return ret; // emits code to drop `y`
    }
    // *not* merge point (only one path, the else branch, flows here)

    //                                  {     x, y }
    if b() {
        //                                  { x, y }
        let ret = f(y);
        //                                  { x    }
        return ret; // emits code to drop `x`
    }

    //                                  {     x, y }

    return 0; // emits code to drop `x` and `y`
}
