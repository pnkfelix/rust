// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(struct_variant)]
#![feature(lang_items)]

#![no_std]
#![crate_type="lib"]

#![allow(unused_variable)]
#![allow(non_camel_case_types)]

#[lang = "owned_box"]
pub struct Box<T>(*mut T);

#[lang="exchange_malloc"]
#[inline]
unsafe fn exchange_malloc(size: uint, align: uint) -> *mut u8 {
    loop { }
}

#[lang="exchange_free"]
unsafe fn exchange_free(ptr: *mut u8, size: uint, align: uint) {
    loop { }
}

mod marker {
    #[lang="no_copy_bound"]
    pub struct NoCopy;
}

struct Foo {
    x: uint,
    b: bool,
    marker: marker::NoCopy
}

fn field_read(f: Foo) -> uint {
    f.x * f.x
}

enum XYZ {
    X,
    Y {
        b: i64,
        c: Box<char>,
    },
    Z {
        b: i32,
        c: Box<char>,
    },
}

fn field_match_in_patterns(b: XYZ) -> Box<char> {
    match b {
        Y { c: c, .. } => c,
        _ => box 'c'
    }
}

struct Bar {
    x: uint,
    b: bool,
}

#[repr(C)]
struct Baz {
    x: u32,
}

fn field_match_in_let(f: Bar) -> bool {
    let Bar { b, .. } = f;
    b
}

pub fn main() {
    field_read(Foo { x: 1, b: false, marker: marker::NoCopy });
    field_match_in_patterns(X);
    field_match_in_let(Bar { x: 42u, b: true });
    let _ = Baz { x: 0 };
}
