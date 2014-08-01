#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub enum Option<T> { None, Some(T), }

mod marker {
    #[lang="no_send_bound"]
    pub struct NoSend;
}

#[lang="gc"]
pub struct Gc<T> {
    _ptr: *mut T,
    marker: marker::NoSend,
}

pub fn foo<T>(c: || -> Option<Gc<T>>, f: |Gc<T>| -> int) -> int {
    let s = c();
    //                                                          // NEEDS_DROP={}
    let ret = match s {
        //                                                      // NEEDS_DROP={}
        Some(x) => {  // Variable s moved in this branch ...
            f(x)
                //                                              // NEEDS_DROP={}
        }
        None => {     // ... but not this one ...
            3
                //                                              // NEEDS_DROP={}
        }
    }; // ... but since it is Gc<T>, needs-drop = {}.
    //        (Gc should not impose drop obligation, even
    //         when T itself may need drop-glue.)
    //                                                          // NEEDS_DROP={}
    c();
    ret
}
