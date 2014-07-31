#![feature(lang_items)]
#![no_std]
#![crate_type="lib"]

#[lang="copy"]  pub trait Copy { }
#[lang="sized"] pub trait Sized { }

pub struct Foo<X,Y> { _x: X, _y: Y, _z: X, _w: X }

pub fn foo<X,Y>(b: || -> bool, c: || -> Foo<X,Y>, f: |Foo<X,Y>| -> i8) -> i8 {
    //                                                       // NEEDS_DROP={}
    let s = c();
    //                                                       // NEEDS_DROP={s}
    if !b() {
        //                                                   // NEEDS_DROP={s}
        f(s) // s moved in this branch ...
            //                                               // NEEDS_DROP={}
    } else {
        //                                                   // NEEDS_DROP={s}
        if b() {
            //                                               // NEEDS_DROP={s}
            f(s) // s moved in this branch ...
            //                                               // NEEDS_DROP={}
        } else {
            //                                               // NEEDS_DROP={s}
            3    // ... but not this one ...
        } // ... thus expect notice at this join-point ...
        // ... but what about the outer merge point ...
        //                                                   // NEEDS_DROP=merge({}, {s})
        // ... we need to choose some value for NEEDS_DROP ...
        // ... we could use union (A | B) ...
        // ... but instead we choose intersection ...
        //                                                   //      ...  = {} & {s}
        // ... (see extensive discussion of why in impl
        // BitwiseOperator for NeedsDropDataFlowOperator) ...
        //                                                   //      ...  = {}
    } // ... thus do *not* expect notice at this joint point.
}
