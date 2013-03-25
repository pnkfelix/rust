// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::prelude::*;

use middle::ty;

use core::task::local_data;
use syntax::ast;
use std::serialize::{Decoder, Decodable};
use std::ebml;
use util::ppaux::ty_to_str;
use metadata::compact;

type ConvertDefIdFn = &'self fn(ast::def_id) -> ast::def_id;

pub fn parse_ty_data(tcx: ty::ctxt,
                     _crate_num: ast::crate_num,
                     doc: ebml::Doc,
                     conv_def_id: ConvertDefIdFn) -> ty::t
{
    let dcx = @ctxt {tcx: tcx, conv_def_id: conv_def_id};
    do ctxt::set(dcx) {
        compact::decode(doc)
    }
}

pub fn parse_arg_data(tcx: ty::ctxt,
                      _crate_num: ast::crate_num,
                      doc: ebml::Doc,
                      conv_def_id: ConvertDefIdFn) -> ty::arg
{
    let dcx = @ctxt {tcx: tcx, conv_def_id: conv_def_id};
    do ctxt::set(dcx) {
        compact::decode(doc)
    }
}

pub fn parse_bounds_data(tcx: ty::ctxt,
                         _crate_num: ast::crate_num,
                         doc: ebml::Doc,
                         conv_def_id: ConvertDefIdFn) -> @~[ty::param_bound]
{
    let dcx = @ctxt {tcx: tcx, conv_def_id: conv_def_id};
    do ctxt::set(dcx) {
        compact::decode(doc)
    }
}

struct ctxt<'self> {
    tcx: ty::ctxt,
    conv_def_id: ConvertDefIdFn<'self>
}

// Horrible hack: the TLS API cannot handle borrowed pointers.  We need a
// dynamically scoped variable API that permits borrowed pointers but is
// restricted to a stack discipline like the one here.
fn ctxtKey(+_v: @*()) {}

impl<'self> ctxt<'self> {
    fn get<R>(op: &fn(@ctxt) -> R) -> R {
        let ctxt: @ctxt = unsafe {
            let ptr: @*() = local_data::local_data_get(ctxtKey).get();
            fail_unless!(ptr.is_not_null());
            cast::transmute(ptr)
        };
        return op(ctxt);
    }

    fn set<R>(ecx: @ctxt, op: &fn() -> R) -> R {
        unsafe {
            let ptr: @*() = cast::transmute(ecx);
            local_data::local_data_set(ctxtKey, ptr);
        }
        let r = op();
        unsafe {
            local_data::local_data_set(ctxtKey, @ptr::null());
        }
        return r;
    }
}

impl<D:Decoder> Decodable<D> for ty::t {
    fn decode(d: &D) -> ty::t {
        do ctxt::get |dcx| {
            debug!(">>");
            let sty: ty::sty = Decodable::decode(d);
            debug!("Decoded sty: %?", sty);
            let sty = remap_sty(dcx, sty);
            debug!("Remapped sty: %?", sty);
            let o_def_id: Option<ast::def_id> = Decodable::decode(d);
            debug!("Decoded o_def_id: %?", o_def_id);
            let t = ty::mk_t_with_id(dcx.tcx, sty, o_def_id);
            debug!("Type = %u %s", ty::type_id(t), ty_to_str(dcx.tcx, t));
            debug!("<<");
            t
        }
    }
}

// Eventually this should be moved into the Encodable rule for def-id!
fn remap_sty(dcx: @ctxt, +s: ty::sty) -> ty::sty {
    match s {
        // Structural types (no embedded def-ids)
        ty::ty_nil => ty::ty_nil,
        ty::ty_bot => ty::ty_bot,
        ty::ty_bool => ty::ty_bool,
        ty::ty_int(a) => ty::ty_int(a),
        ty::ty_uint(a) => ty::ty_uint(a),
        ty::ty_float(a) => ty::ty_float(a),
        ty::ty_estr(a) => ty::ty_estr(a),
        ty::ty_box(a) => ty::ty_box(a),
        ty::ty_uniq(a) => ty::ty_uniq(a),
        ty::ty_evec(a, b) => ty::ty_evec(a, b),
        ty::ty_ptr(a) => ty::ty_ptr(a),
        ty::ty_rptr(a, b) => ty::ty_rptr(a, b),
        ty::ty_bare_fn(a) => ty::ty_bare_fn(a),
        ty::ty_closure(a) => ty::ty_closure(a),
        ty::ty_tup(a) => ty::ty_tup(a),
        ty::ty_self(a) => ty::ty_self((dcx.conv_def_id)(a)),
        ty::ty_err => ty::ty_err,
        ty::ty_type => ty::ty_type,
        ty::ty_opaque_box => ty::ty_opaque_box,
        ty::ty_opaque_closure_ptr(a) => ty::ty_opaque_closure_ptr(a),
        ty::ty_unboxed_vec(a) => ty::ty_unboxed_vec(a),
        ty::ty_param(ty::param_ty {idx, def_id}) => {
            ty::ty_param(
                ty::param_ty {idx: idx,
                              def_id: (dcx.conv_def_id)(def_id)})
        }
        ty::ty_enum(def_id, substs) => {
            ty::ty_enum((dcx.conv_def_id)(def_id), substs)
        }
        ty::ty_trait(def_id, substs, store) => {
            ty::ty_trait((dcx.conv_def_id)(def_id), substs, store)
        }
        ty::ty_struct(def_id, substs) => {
            ty::ty_struct((dcx.conv_def_id)(def_id), substs)
        }
        ty::ty_infer(a) => {
            dcx.tcx.sess.bug(
                fmt!("Encountered ty_infer when decoding type: %?", a));
        }
    }
}
