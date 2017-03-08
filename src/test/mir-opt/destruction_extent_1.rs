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

fn main() {
    let d0 = D(0, None);
    let d1 = D(1, Some(&d0));
    let d2 = {
        let d3 = D(3, Some(&d0));
        D(2, Some(&d1))
    };
    foo(d1.0);
}

#[derive(Debug)]
struct D<'a>(i32, Option<&'a D<'a>>);
impl<'a> Drop for D<'a> { fn drop(&mut self) { println!("dropping D({}, {:?})", self.0, self.1); } }

fn foo(i: i32) {
    if i > 0 { panic!("im positive"); }
}
