// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(box_syntax)]
#![feature(const_fn)]

use std::cell::RefCell;

// Regression test for issue 7364
static boxed: Box<RefCell<isize>> = box RefCell::new(0);
//~^ ERROR statics are not allowed to have destructors
//~| ERROR statics are not allowed to have destructors
//~| ERROR statics are not allowed to have destructors
//~| ERROR the trait `core::marker::Sync` is not implemented for the type
//~| ERROR the trait `core::marker::Sync` is not implemented for the type
//~| ERROR blocks in statics are limited to items and tail expressions
//~| ERROR blocks in statics are limited to items and tail expressions
//~| ERROR blocks in statics are limited to items and tail expressions
//~| ERROR paths in statics may only refer to constants or functions
//~| ERROR paths in statics may only refer to constants or functions
//~| ERROR paths in statics may only refer to constants or functions
//~| ERROR function calls in statics are limited to constant functions, struct and enum constructors
//~| ERROR function calls in statics are limited to constant functions, struct and enum constructors
//~| ERROR function calls in statics are limited to constant functions, struct and enum constructors
//~| ERROR function calls in statics are limited to constant functions, struct and enum constructors
//~| ERROR references in statics may only refer to immutable values

fn main() { }
