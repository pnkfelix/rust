// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(nll)]

// This test is a minimal version of an ICE in the dropck-eyepatch tests
// found in the fix for #54943.

// compile-pass

fn foo<T>(_t: T) {
}

fn main() {
    struct A<'a, B: 'a>(&'a B);
    let (a1, a2): (String, A<_>) = (String::from("auto"), A(&"this"));
    foo((a1, a2));
}
