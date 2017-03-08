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

// Unwinding should EndRegion for in-scope borrows.

fn main() {
    let d = D(0);
    let a = 0;
    let b = &a;
    foo(|| -> i32 { let r = &d; r.0 });
    let c = &a;
}

struct D(i32);
impl Drop for D { fn drop(&mut self) { println!("dropping D({})", self.0); } }

fn foo<F>(f: F) where F: FnOnce() -> i32 {
    if f() > 0 { panic!("im positive"); }
}

// END RUST SOURCE
// START rustc.node4.TypeckMir.before.mir
//     bb0: {
//         StorageLive(_1);
//         _1 = D::{{constructor}}(const 0i32,);
//         StorageLive(_3);
//         _3 = const 0i32;
//         StorageLive(_4);
//         _4 = &'21ce _3;
//         StorageLive(_6);
//         _6 = (*_4);
//         _5 = foo(_6) -> [return: bb3, unwind: bb2];
//     }
//
//     bb1: {
//         resume;
//     }
//
//     bb2: {
//         EndRegion('21ce);
//         drop(_1) -> bb1;
//     }
//
//     bb3: {
//         StorageDead(_6);
//         StorageLive(_7);
//         _7 = &'33ce _3;
//         StorageDead(_7);
//         EndRegion('33ce);
//         StorageDead(_4);
//         EndRegion('21ce);
//         StorageDead(_3);
//         drop(_1) -> bb4;
//     }
//
//     bb4: {
//         StorageDead(_1);
//         return;
//     }
// END rustc.node4.TypeckMir.before.mir
