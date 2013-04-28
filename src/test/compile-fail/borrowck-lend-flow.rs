// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Note: the borrowck analysis is currently flow-insensitive.
// Therefore, some of these errors are marked as spurious and could be
// corrected by a simple change to the analysis.  The others are
// either genuine or would require more advanced changes.  The latter
// cases are noted.

fn borrow(_v: &int) {}

fn borrow_mut(_v: &mut int) {}

fn inc(v: &mut ~int) {
    *v = ~(**v + 1);
}

fn post_aliased_const() {
    // In this instance, the const alias starts after the borrow.

    let mut v = ~3;
    borrow(v);
    let _w = &const v;
}

fn post_aliased_mut() {
    // In this instance, the mutable borrow starts after the immutable borrow.

    let mut v = ~3;
    borrow(v);
    let w = &mut v;
    *w = ~5;
}

fn post_aliased_scope(cond: bool) {
    // In this instance, the mutable alias starts after the borrow,
    // but it is also ruled out because of the scope.

    let mut v = ~3;
    borrow(v);
    if cond { inc(&mut v); }
}

fn loop_overarching_alias_mut() {
    // In this instance, the borrow encompasses the entire loop.

    let mut v = ~3;
    let mut x = &mut v;
    loop {
        borrow(v); //~ ERROR cannot borrow
    }
    *x = ~5;
}

fn block_overarching_alias_mut() {
    // In this instance, the borrow encompasses the entire closure call.

    let mut v = ~3;
    let mut x = &mut v;
    for 3.times {
        borrow(v); //~ ERROR cannot borrow
    }
    *x = ~5;
}

fn loop_aliased_mut() {
    // In this instance, the borrow is carried through the loop.

    let mut v = ~3, w = ~4;
    let mut x = &mut w;
    loop {
        **x += 1;
        borrow(v); //~ ERROR cannot borrow
        x = &mut v; //~ ERROR cannot borrow
    }
}

fn while_aliased_mut(cond: bool) {
    // In this instance, the borrow is carried through the while loop.

    let mut v = ~3, w = ~4;
    let mut x = &mut w;
    while cond {
        **x += 1;
        borrow(v); //~ ERROR cannot borrow
        x = &mut v;
    }
}

fn while_aliased_mut_cond(cond: bool, cond2: bool) {
    let mut v = ~3, w = ~4;
    let mut x = &mut w;
    while cond {
        **x += 1;
        borrow(v); //~ ERROR cannot borrow
        if cond2 {
            x = &mut v;
        }
    }
}

fn loop_in_block() {
    let mut v = ~3, w = ~4;
    let mut x = &mut w;
    for uint::range(0u, 10u) |_i| {
        **x += 1;
        borrow(v); //~ ERROR cannot borrow
        x = &mut v;
    }
}

fn at_most_once_block() {
    fn at_most_once(f: &fn()) { f() }

    // Here, the borrow check has no way of knowing that the block is
    // executed at most once.

    let mut v = ~3, w = ~4;
    let mut _x = &mut w;
    do at_most_once {
        borrow(v); //~ ERROR loan of mutable local variable as immutable cannot borrow
        _x = &mut v; //~ NOTE prior loan as mutable granted here
    }
}

fn main() {}
