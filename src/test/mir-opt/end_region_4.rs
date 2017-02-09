// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// compile-flags: -Z identify_regions
// ignore-tidy-linelength

struct D(i32);
impl Drop for D { fn drop(&mut self) { println!("dropping D({})", self.0); } }

fn main() {
    let d = D(0);
    let a = 3;
    let b = &a;
    foo(*b);
    let c = &a;
}

fn foo(i: i32) {
    if i > 3 { panic!("im positive"); }
}

// END RUST SOURCE
// START rustc.node4.TypeckMir.before.mir
//     bb0: {
//         StorageLive(_1);
//         _1 = const 0usize;
//         StorageLive(_2);
//         _2 = &'14ce _1;
//     }
// END rustc.node4.TypeckMir.before.mir
