#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

mod marker {
    #[lang="no_send_bound"]
    pub struct NoSend;
}

#[lang="gc"]
pub struct Gc<T> {
    _ptr: *mut T,
    marker: marker::NoSend,
}

pub fn foo<T>(b: bool, c: || -> Gc<T>, f: |Gc<T>| -> int) -> int {
    let x = c();
    //                                                          // NEEDS_DROP={}
    let ret = if b {
    //                                                          // NEEDS_DROP={}
        f(x) // Variable x copied in this branch ...
    //                                                          // NEEDS_DROP={}
    } else {
    //                                                          // NEEDS_DROP={}
        3    // ... but not this one ...
    //                                                          // NEEDS_DROP={}
    }; // ... but since it is Gc<T>, needs-drop = {}.
    //        (Gc should not impose drop obligation, even
    //         when T itself may need drop-glue.)
    //                                                          // NEEDS_DROP={}
    c();
    ret
}
