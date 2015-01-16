// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cell::Cell;

struct D<'a> {
    p: Cell<Option<&'a D<'a>>>,
}

impl<'a> D<'a> {
    fn new() -> D<'a> { D { p: Cell::new(None) } }
}

impl<'a> Drop for D<'a> {
    fn drop(&mut self) { }
}

fn g() {
    let (d1, d2) = (D::new(), D::new());
    d1.p.set(Some(&d2)); //~ ERROR `d2` does not live long enough
    d2.p.set(Some(&d1)); //~ ERROR `d1` does not live long enough
}

fn main() {
    g();
}
