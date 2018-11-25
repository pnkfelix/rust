// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(nll)]

fn static_to_a_to_static_through_ref_in_tuple<'a>(x: &'a u32) -> &'static u32 {
    let (ref y, _z): (&'a u32, u32) = (&22, 44);
    *y //~ ERROR
}

fn main() {}
