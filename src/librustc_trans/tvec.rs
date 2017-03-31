// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use llvm;
use builder::Builder;
use llvm::{BasicBlockRef, ValueRef};
use common::*;
use rustc::ty::Ty;

pub fn slice_for_each<'a, 'tcx, F>(
    bcx: &Builder<'a, 'tcx>,
    data_ptr: ValueRef,
    unit_ty: Ty<'tcx>,
    len: ValueRef,
    f: F
) -> Builder<'a, 'tcx> where F: FnOnce(&Builder<'a, 'tcx>, ValueRef, BasicBlockRef) {
    slice_for_each_gen(bcx, data_ptr, unit_ty, len, f, Dir::Fwd)
}

pub fn slice_for_each_rev<'a, 'tcx, F>(
    bcx: &Builder<'a, 'tcx>,
    data_ptr: ValueRef,
    unit_ty: Ty<'tcx>,
    len: ValueRef,
    f: F
) -> Builder<'a, 'tcx> where F: FnOnce(&Builder<'a, 'tcx>, ValueRef, BasicBlockRef) {
    slice_for_each_gen(bcx, data_ptr, unit_ty, len, f, Dir::Rev)
}

enum Dir { Fwd, Rev }

fn slice_for_each_gen<'a, 'tcx, F>(
    bcx: &Builder<'a, 'tcx>,
    data_ptr: ValueRef,
    unit_ty: Ty<'tcx>,
    len: ValueRef,
    f: F,
    direction: Dir
) -> Builder<'a, 'tcx> where F: FnOnce(&Builder<'a, 'tcx>, ValueRef, BasicBlockRef) {
    // Special-case vectors with elements of size 0  so they don't go out of bounds (#9890)
    let zst = type_is_zero_size(bcx.ccx, unit_ty);
    let add = |bcx: &Builder, a, b| if zst {
        bcx.add(a, b)
    } else {
        bcx.inbounds_gep(a, &[b])
    };

    let body_bcx = bcx.build_sibling_block("slice_loop_body");
    let next_bcx = bcx.build_sibling_block("slice_loop_next");
    let header_bcx = bcx.build_sibling_block("slice_loop_header");

    // For non-zst, Dir::Fwd generates:
    //   c = &data[0]; f = &data[len]; while (c != f) { n = c+1; visit(c); c = n; }
    //
    // while Dir::Rev generates:
    //   c = &data[len]; f = &data[0]; while (c > f)  { n = c-1; visit(n); c = n; }

    let (init, fini, cmp_op, stride) = {
        let start = if zst {
            C_uint(bcx.ccx, 0usize)
        } else {
            data_ptr
        };
        let end = add(&bcx, start, len);

        match direction {
            Dir::Fwd => (start, end, llvm::IntNE, 1isize),
            Dir::Rev => (end, start, llvm::IntUGT, -1isize),
        }
    };

    bcx.br(header_bcx.llbb());
    let current = header_bcx.phi(val_ty(init), &[init], &[bcx.llbb()]);

    let keep_going = header_bcx.icmp(cmp_op, current, fini);
    header_bcx.cond_br(keep_going, body_bcx.llbb(), next_bcx.llbb());

    let next = add(&body_bcx, current, C_uint(bcx.ccx, stride as usize));
    let visit_target = match direction { Dir::Fwd => current, Dir::Rev => next };
    f(&body_bcx, if zst { data_ptr } else { visit_target }, header_bcx.llbb());
    header_bcx.add_incoming_to_phi(current, next, body_bcx.llbb());
    next_bcx
}
