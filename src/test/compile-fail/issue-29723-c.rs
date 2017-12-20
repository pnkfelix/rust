// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// revisions: ast mir migrate
//[ast]compile-flags: -Z borrowck=ast
//[mir]compile-flags: -Z borrowck=mir
//[migrate]compile-flags: -Z borrowck=migrate

#![feature(rustc_attrs)]

use std::cell::RefCell;

fn assign<'a, 'b>(x: &RefCell<Option<&'a &'b mut u32>>, y: &'a &'b mut u32) {
    *x.borrow_mut() = Some(y);
}

fn unsound<'a>(opt: &'a mut Option<&'a mut u32>) -> Option<&'a mut u32> {
    let store: RefCell<Option<&&mut u32>> = RefCell::new(None);
    match *opt {
        #[cfg(not(should_be_fine))]
        Some(ref mut x) if {
            // this (making `x` escape from the arm) should be disallowed
            // - `x` shouldn't be `&'a mut &'a mut u32` here
            assign(&store, x);
            false
        } => {
           None
        }
        #[cfg(should_be_fine)]
        Some(ref mut x) if { false } => {
            // but just using `x` should be fine: `x` has the type `&'a mut &'a mut u32` here
            Some(x)
        }
        ref mut x => {
            //[mir]~^      ERROR cannot borrow `*opt` as mutable more than once at a time [E0499]
            //[migrate]~^^ WARN  cannot borrow `*opt` as mutable more than once at a time [E0499]
            //[migrate]~|  WARN  will become a hard error in a future release
            *x = None;
            println!("{:?}", store.borrow());
            None
        }
    }
}

fn foo() {
    let (mut t, mut ten);
    ten = 10;
    t = Some(&mut ten);
    unsound(&mut t);
}

#[rustc_error]
fn main() { //[ast]~ ERROR: compilation successful
    //[migrate]~^    ERROR: compilation successful
    foo();
}
