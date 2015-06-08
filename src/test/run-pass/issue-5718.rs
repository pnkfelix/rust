// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// no-pretty-expanded FIXME #26067

#![allow(unknown_features)]
#![feature(box_syntax)]

struct Element;

macro_rules! foo {
    ($tag: expr, $string: expr) => {
        if $tag == $string {
            let element: Box<_> = box Element;
            unsafe {
                return std::mem::transmute::<_, usize>(element);
            }
        }
    }
}

fn bar() -> usize {
    foo!("a", "b");
    0
}

fn main() {
    bar();
}
