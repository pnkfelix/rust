// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// compile-flags: -Z identify_regions -Z span_free_formats
// ignore-tidy-linelength

// Unwinding should EndRegion for in-scope borrows: 2nd borrow within by-ref closure.

fn main() {
    let d = D(0);
    foo(|| -> i32 { let r = &d; r.0 });
}

struct D(i32);
impl Drop for D { fn drop(&mut self) { println!("dropping D({})", self.0); } }

fn foo<F>(f: F) where F: FnOnce() -> i32 {
    if f() > 0 { panic!("im positive"); }
}

// END RUST SOURCE
// START rustc.node4.SimplifyCfg.qualify-consts-after.mir
//     let mut _0: ();
//     let _1: D;
//     let mut _2: ();
//     let mut _3: ();
//     let mut _4: [closure@NodeId(22) d:&'18ce D];
//     let mut _5: &'18ce D;
//
//     bb0: {
//         StorageLive(_1);
//         _1 = D::{{constructor}}(const 0i32,);
//         StorageLive(_4);
//         StorageLive(_5);
//         _5 = &'18ce _1;
//         _4 = [closure@NodeId(22)] { d: _5 };
//         StorageDead(_5);
//         _3 = const foo(_4) -> [return: bb3, unwind: bb2];
//     }
//     bb1: {
//         resume;
//     }
//     bb2: {
//         EndRegion('18ce);
//         drop(_1) -> bb1;
//     }
//     bb3: {
//         StorageDead(_4);
//         EndRegion('18ce);
//         _0 = ();
//         drop(_1) -> bb4;
//     }
//     bb4: {
//         StorageDead(_1);
//         return;
//     }
// END rustc.node4.SimplifyCfg.qualify-consts-after.mir

// START rustc.node22.SimplifyCfg.qualify-consts-after.mir
// fn main::{{closure}}(_1: [closure@NodeId(22) d:&'18ce D]) -> i32 {
//     let mut _0: i32;
//     let _2: &'25ce D;
//     let mut _4: i32;
//
//     bb0: {
//         StorageLive(_2);
//         _2 = &'25ce (*(_1.0: &'18ce D));
//         StorageLive(_4);
//         _4 = ((*_2).0: i32);
//         _0 = _4;
//         StorageDead(_4);
//         StorageDead(_2);
//         EndRegion('25ce);
//         return;
//     }
// END rustc.node22.SimplifyCfg.qualify-consts-after.mir
