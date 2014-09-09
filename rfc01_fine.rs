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

struct Pair<X,Y>{ x:X, y:Y }

struct D; struct S;

impl Drop for D { fn drop(&mut self) { loop { } } }

fn test() -> bool { loop { } }

fn xform(d:D) -> D { loop { } }

fn foo(mk_dd: || -> Pair<D,D>, mk_ds: || -> Pair<D,S>, mk_opt_d: || -> Option<D>) {
    // At the outset, the set of drop obligations is
    // just the set of moved input parameters (empty
    // in this case).

    //                                      DROP OBLIGATIONS
    //                                  ------------------------
    //                                  {  }
    let mut pDD : Pair<D,D> = mk_dd();
    //                                  { pDD.x, pDD.y }
    let pDS : Pair<D,S> = mk_ds();
    //                                  { pDD.x, pDD.y, pDS.x }
    let mut some_d : Option<D> = mk_opt_d();
    //                                  { pDD.x, pDD.y, pDS.x }
    if test() {
        //                                 { pDD.x, pDD.y, pDS.x }
        {
            let temp = xform(pDD.x);
            //                             {        pDD.y, pDS.x, temp }
            some_d = Some(temp);
            //                             {        pDD.y, pDS.x, temp, some_d }
        } // END OF SCOPE for `temp`
        //                                 {        pDD.y, pDS.x, some_d }
    } else {
        {
            //                             { pDD.x, pDD.y, pDS.x }
            let z = D;
            //                             { pDD.x, pDD.y, pDS.x, z }

            // This drops `pDD.y` before
            // moving `pDD.x` there.
            pDD.y = pDD.x;

            //                             {        pDD.y, pDS.x, z }
            some_d = None;
            //                             {        pDD.y, pDS.x, z, some_d }
        } // END OF SCOPE for `z`
        //                                 {        pDD.y, pDS.x, some_d }
    }

    // MERGE POINT: set of drop obligations must
    // match on all incoming control-flow paths...
    //
    // ... which they do in this case.

    //                                  {       pDD.y, pDS.x, some_d }

    // (... some code that does not change drop obligations ...)
    mk_dd();

    //                                  {       pDD.y, pDS.x, some_d }
}
