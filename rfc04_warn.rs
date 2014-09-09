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

        if test() {
            //                                  { pDD.x, pDD.y }
            break 'a;
        }

        // never falls through; must merge with 'a loop.
    }

    // MERGE POINT: both `break 'a;` statements above flow here ...
    //
    // ... and their drop obligations do not match, so we get a
    // warning here.

    //                                  {                pDD.y }

    // (... some code that does not change drop obligations ...)
    mk_dd();

    //                                  {               pDD.y }
}
