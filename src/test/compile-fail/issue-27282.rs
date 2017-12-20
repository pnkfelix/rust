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

fn foo() {
    match Some(&4) {
        None => {},
        ref mut foo
            if {
                (|| { let bar = foo; bar.take() })();
                false
            } => {},
        Some(s) => println!("{}", *s)
        //[mir]~^       ERROR [E0503]
        //[mir]~|       ERROR [E0503]
        //[migrate]~^^^  WARN [E0503]
        //[migrate]~|    WARN will become a hard error in a future release
        //[migrate]~|    WARN [E0503]
        //[migrate]~|    WARN will become a hard error in a future release
    }
}

#[rustc_error]
fn main() { //[ast]~ ERROR: compilation successful
    //[migrate]~^    ERROR: compilation successful
}
