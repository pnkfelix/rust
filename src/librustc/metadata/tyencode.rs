// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


// Type encoding

use core::prelude::*;

use core::io;
use core::task::local_data;
use std::oldmap::HashMap;
use std::json;
use std::serialize::{Encoder, Encodable};
use syntax::ast::*;
use syntax::diagnostic::span_handler;
use middle::ty;
use metadata::compact;

pub fn encode_ty(wr: @io::Writer, t: ty::t) {
    compact::encode(wr, &t);
}

pub fn encode_ty_to_str(wr: @io::Writer, t: ty::t) {
    let json_w = json::Encoder(wr);
    t.encode(&json_w);
}

pub fn encode_arg(wr: @io::Writer, arg: ty::arg) {
    compact::encode(wr, &arg);
}

pub fn encode_bounds(wr: @io::Writer,
                     bounds: @~[ty::param_bound]) {
    compact::encode(wr, &bounds);
}

pub fn encode_vstore(wr: @io::Writer,
                     vstore: ty::vstore) {
    compact::encode(wr, &vstore)
}

impl<S:Encoder> Encodable<S> for ty::t {
    fn encode(&self, s: &S) {
        let b = ty::get(*self);
        b.sty.encode(s);
        b.o_def_id.encode(s);
    }
}
