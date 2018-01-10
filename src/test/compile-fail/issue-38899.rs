// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ignore-tidy-linelength
// revisions: ast mir migrate
//[ast]compile-flags: -Z borrowck=ast
//[mir]compile-flags: -Z borrowck=mir
//[migrate]compile-flags: -Z borrowck=migrate

#![feature(rustc_attrs)]

#![allow(dead_code)]
pub struct Block<'a> {
    current: &'a u8,
    unrelated: &'a u8,
}

fn bump<'a>(mut block: &mut Block<'a>) {
    let x = &mut block;
    let p: &'a u8 = &*block.current;
    //[mir]~^      ERROR cannot borrow `*block.current` as immutable because it is also borrowed as mutable [E0502]
    //[migrate]~^^ WARN  cannot borrow `*block.current` as immutable because it is also borrowed as mutable [E0502]
    //[migrate]~|  WARN will become a hard error in a future release

    // artificially extend borrows to end of block.
    drop(x);
    drop(p);
}

#[rustc_error]
fn main() { //[ast]~ ERROR: compilation successful
    //[migrate]~^    ERROR: compilation successful
}
