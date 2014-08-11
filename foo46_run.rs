#![feature(lang_items)]

pub struct Foo<X,Y> { _x: X, _y: Y, z: Option<OneOhOne> }

pub struct OneOhOne {
    ptr: *mut int
}

impl Drop for OneOhOne {
    fn drop(&mut self) {
        unsafe {
            *self.ptr = 101;
        }
    }
}

fn main() {
    let r = foo(true, || { Foo { _x: 1i, _y: 2i, z: None } }, |_| 10i, |_| 11i);
    println!("r: {}", r);
}

pub fn foo<X,Y:Copy>(b: bool, c: || -> Foo<X,Y>, f: |X| -> int, _g: |Y| -> int) -> int {
    let mut ret = 4;
    let mut s = c();
    {
        s.z = Some(OneOhOne { ptr: &mut ret as *mut int });
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

    match true {
        #[cfg(illustrate)]
        true => std::mem::drop(s.z),
        _ => {}
    }

    ret
}
