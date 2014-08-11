#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }
#[lang="drop"] pub trait Drop { fn drop(&mut self); }

pub enum Option<T> { None, Some(T), }

pub struct Foo<X,Y> { _x: X, _y: Y, z: OneOhOne }

pub struct OneOhOne {
    ptr: Option<*mut int>
}

impl Drop for OneOhOne {
    fn drop(&mut self) {
        match self.ptr {
            None => {}
            Some(ptr) => {
                unsafe {
                    *ptr = 101;
                }
            }
        }
    }
}

pub fn foo<X,Y:Copy>(b: bool, c: || -> Foo<X,Y>, f: |X| -> int, _g: |Y| -> int) -> int {
    let mut ret = 4;
    let mut s = c();
    {
        s.z = OneOhOne { ptr: Some(&mut ret as *mut int) };
        //                                                          // NEEDS_DROP={s}
        if b {
            //                                                          // NEEDS_DROP={s}
            f(s._x) // Path s._x moved in this branch ...
                //                                                          // NEEDS_DROP={}
        } else {
            //                                                          // NEEDS_DROP={s}
            3    // ... but not this one ...
                //                                                          // NEEDS_DROP={s}
        }; // ... but the only thing remaining is a read, so ... is it fine?
    }
    ret
}
