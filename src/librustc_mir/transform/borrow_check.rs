// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This pass borrow-checks the MIR to (further) ensure it is not broken.

use rustc::ty::TyCtxt;
use rustc::mir::{Mir};
use rustc::mir::transform::{MirPass, MirSource, Pass};

pub struct BorrowckMir;

impl<'tcx> MirPass<'tcx> for BorrowckMir {
    fn run_pass<'a>(&mut self, tcx: TyCtxt<'a, 'tcx, 'tcx>,
                    src: MirSource, _mir: &mut Mir<'tcx>) {
        debug!("run_pass BorrowckMir: {}", tcx.node_path_str(src.item_id()));

        if tcx.sess.err_count() > 0 {
            // compiling a broken program can obviously result in a
            // broken MIR, so try not to report duplicate errors.
            return;
        }
    }
}

impl Pass for BorrowckMir {

}
