// Copyright 2012-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::middle::region::CodeExtent;
use rustc::mir::{self, Location};
use rustc::ty;

use std::fmt;

pub(crate) use dataflow::indexes::BorrowIndex;
pub(crate) use dataflow::impls::borrows::Borrows;

// temporarily allow some dead fields: `kind` and `region` will be
// needed by borrowck; `lvalue` will probably be a MovePathIndex when
// that is extended to include borrowed data paths.
#[allow(dead_code)]
#[derive(Debug)]
pub struct BorrowData<'tcx> {
    pub(crate) location: Location,
    pub(crate) kind: mir::BorrowKind,
    pub(crate) region: CodeExtent,
    pub(crate) lvalue: mir::Lvalue<'tcx>,
}

impl<'tcx> fmt::Display for BorrowData<'tcx> {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        let kind = match self.kind {
            mir::BorrowKind::Shared => "",
            mir::BorrowKind::Unique => "uniq ",
            mir::BorrowKind::Mut => "mut ",
        };
        let region = format!("{}", ty::ReScope(self.region));
        let region = if region.len() > 0 { format!("{} ", region) } else { region };
        write!(w, "&{}{}{:?}", region, kind, self.lvalue)
    }
}
