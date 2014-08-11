#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }
#[lang="drop"] pub trait Drop { fn drop(&mut self); }

pub enum Option<T> { None, Some(T), }

pub struct Foo<'a,X,Y> { _x: X, _y: Y, z: Option<&'a mut int> }

pub fn foo<X,Y:Copy>(b: bool, c: <'a> || -> Foo<'a,X,Y>, f: |X| -> int, _g: |Y| -> int) -> int {
    let mut ret = 4;
    {
        let mut s = c();
        s.z = Some(&mut ret);
        //                                                          // NEEDS_DROP={s}
        if b {
            //                                                          // NEEDS_DROP={s}
            f(s._x) // Path s._x moved in this branch ...
                //                                                          // NEEDS_DROP={}
        } else {
            //                                                          // NEEDS_DROP={s}
            3    // ... but not this one ...
                //                                                          // NEEDS_DROP={s}
        }; // ... but the only thing remaining is a read, so fine.
    }
    ret
}
