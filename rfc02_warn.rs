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

// `f2` is similar to `f1`, except that it will have differing set
// of drop obligations at the merge point, necessitating a hidden
// drop call.
fn foo(mk_dd: || -> Pair<D,D>, mk_ds: || -> Pair<D,S>, mk_opt_d: || -> Option<D>) {
    // At the outset, the set of drop obligations is
    // just the set of moved input parameters (empty
    // in this case).

    //                                      DROP OBLIGATIONS
    //                                  ------------------------
    //                                  {  }
    let mut pDD : Pair<D,D> = mk_dd();
    //                                  {pDD.x, pDD.y}
    let pDS : Pair<D,S> = mk_ds();
    //                                  {pDD.x, pDD.y, pDS.x}
    let mut some_d : Option<D> = mk_opt_d();
    //                                  {pDD.x, pDD.y, pDS.x}
    if test() {
        //                                  {pDD.x, pDD.y, pDS.x}
        {
            let temp = xform(pDD.y);
            //                              {pDD.x,        pDS.x, temp}
            some_d = Some(temp);
            //                              {pDD.x,        pDS.x, temp, some_d}
        } // END OF SCOPE for `temp`
        //                                  {pDD.x,        pDS.x, some_d}

        // MERGE POINT PREDECESSOR 1

        // implicit drops injected: drop(pDD.y)
    } else {
        {
            //                              {pDD.x, pDD.y, pDS.x}
            let z = D;
            //                              {pDD.x, pDD.y, pDS.x, z}

            // This drops `pDD.y` before
            // moving `pDD.x` there.
            pDD.y = pDD.x;

            //                              {       pDD.y, pDS.x, z}
            some_d = None;
            //                              {       pDD.y, pDS.x, z, some_d}
        } // END OF SCOPE for `z`
        //                                  {       pDD.y, pDS.x, some_d}

        // MERGE POINT PREDECESSOR 2

        // implicit drops injected: drop(pDD.y)
    }

    // MERGE POINT: set of drop obligations must
    // match on all incoming control-flow paths.
    //
    // For the original user code, they did not
    // in this case.
    //
    // Therefore, implicit drops are injected up
    // above, to ensure that the set of drop
    // obligations match.

    // After the implicit drops, the resulting
    // remaining drop obligations are the
    // following:

    //                                  {              pDS.x, some_d}

    // (... some code that does not change drop obligations ...)
    mk_dd();

    //                                  {              pDS.x, some_d}
}
