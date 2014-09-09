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

fn foo(mk_dd: || -> Pair<D,D>, mk_d: || -> D, consume: |D|) {
    // At the outset, the set of drop obligations is
    // just the set of moved input parameters (empty
    // in this case).

    //                                      DROP OBLIGATIONS
    //                                  ------------------------
    //                                  {  }
    let mut pDD : Pair<D,D> = mk_dd();
    //                                  {         pDD.x, pDD.y }
    'a: loop {
        // MERGE POINT: set of drop obligations must
        // match on all incoming control-flow paths.

        //                                  {     pDD.x, pDD.y }
        if test() {
            //                                  { pDD.x, pDD.y }
            consume(pDD.x);
            //                                  {        pDD.y }
            break 'a;
        }

        //                                  {     pDD.x, pDD.y }

        // *not* merge point (only one path flows here)

        // never falls through; must merge with 'a loop.
    }

    // RESUME POINT: break 'a above flows here

    //                                  {                pDD.y }

    'b: loop {
        // MERGE POINT: set of drop obligations must match on all
        // incoming control-flow paths.
        //
        // There are *three* such incoming paths: (1.) the statement
        // preceding `'b: loop`, (2.) the `continue 'b;` below, and
        // (3.) the loop end below.

        //                                  {            pDD.y }

        consume(pDD.y);

        //                                  {                  }

        if test() {
            //                                  {              }
            pDD.y = mk_d();
            //                                  {        pDD.y }
            break 'b;
        }

        // *not* merge point (only one path flows here)

        //                                  {                  }

        if test() {
            //                                  {              }
            pDD.y = mk_d();
            //                                  {        pDD.y }
            continue 'b;
        }
        // *not* merge point (only one path flows here)

        //                                  {                  }

        pDD.y = mk_d();

        //                                  {            pDD.y }
    }

    // RESUME POINT: break 'b above flows here

    //                                  {               pDD.y }

    // (... some code that does not change drop obligations ...)
    mk_dd();

    //                                  {               pDD.y }
}
