// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!

Rust MIR: a lowered representation of Rust. Also: an experiment!

*/

#![crate_name = "rustc_mir"]
#![crate_type = "rlib"]
#![crate_type = "dylib"]
#![deny(warnings)]
#![unstable(feature = "rustc_private", issue = "27812")]

#![feature(associated_consts)]
#![feature(box_patterns)]
#![feature(box_syntax)]
#![cfg_attr(stage0, feature(field_init_shorthand))]
#![feature(i128_type)]
#![cfg_attr(stage0, feature(pub_restricted))]
#![feature(rustc_diagnostic_macros)]
#![feature(rustc_private)]
#![feature(staged_api)]
#![feature(placement_in_syntax)]
#![feature(collection_placement)]
#![feature(nonzero)]

#[macro_use] extern crate log;
extern crate graphviz as dot;
#[macro_use]
extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_errors;
#[macro_use]
#[no_link]
extern crate rustc_bitflags;
#[macro_use]
extern crate syntax;
extern crate syntax_pos;
extern crate rustc_const_math;
extern crate rustc_const_eval;
extern crate core; // for NonZero

pub mod diagnostics;

pub mod build;
pub mod callgraph;
pub mod dataflow;
mod hair;
mod shim;
pub mod mir_map;
pub mod transform;
pub mod util;

use syntax::ast::{self, MetaItem};

use rustc::ty::maps::Providers;

pub fn provide(providers: &mut Providers) {
    mir_map::provide(providers);
    shim::provide(providers);
    transform::qualify_consts::provide(providers);
}

fn has_rustc_mir_with(attrs: &[ast::Attribute], name: &str) -> Option<MetaItem> {
    for attr in attrs {
        if attr.check_name("rustc_mir") {
            let items = attr.meta_item_list();
            for item in items.iter().flat_map(|l| l.iter()) {
                match item.meta_item() {
                    Some(mi) if mi.check_name(name) => return Some(mi.clone()),
                    _ => continue
                }
            }
        }
    }
    return None;
}
