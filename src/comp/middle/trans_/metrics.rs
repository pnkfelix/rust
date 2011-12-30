// A module for managing sizeof/alignment computations.  This is
// particularly tricky in Rust because of the way we handle generics:
// not all types are fully known statically, so the offset and
// alignment of some fields must be resolved dynamically.

import syntax::ast;
import syntax::ast_util;
import lib::llvm::{llvm, True, False};
import llvm::{ValueRef, TypeRef};
import middle::trans_common::*;
import middle::trans_build::*;
import middle::freevars::{get_freevars, freevar_info};
import back::abi;
import syntax::codemap::span;
import back::link::{
    mangle_internal_name_by_path,
    mangle_internal_name_by_path_and_seq};
import util::ppaux::ty_to_str;

export llsize_of;
export llalign_of;
export llsize_of_real;
export llalign_of_real;
export size_of;
export align_of;
export GEP_tup_like;
export GEP_tup_like_1;
export GEP_tag;
export type_of_1;
export type_of;
export type_of_fn;
export type_of_or_i8;
export type_of_inner;
export type_of_ty_param_kinds_and_ty;
export type_of_tag;
export type_of_fn_from_ty;
export type_of_explicit_args;
export native_fn_wrapper_type;
export raw_native_fn_type;

// ______________________________________________________________________
// type_of() and friends
//
// Converts from Rust types to LLVM types.  Works only for types of
// static size.

fn type_of_1(bcx: @block_ctxt, t: ty::t) -> TypeRef {
    let cx = bcx_ccx(bcx);
    check type_has_static_size(cx, t);
    type_of(cx, bcx.sp, t)
}

fn type_of(cx: @crate_ctxt, sp: span, t: ty::t) : type_has_static_size(cx, t)
   -> TypeRef {
    // Should follow from type_has_static_size -- argh.
    // FIXME (requires Issue #586)
    check non_ty_var(cx, t);
    type_of_inner(cx, sp, t)
}

fn type_of_explicit_args(cx: @crate_ctxt, sp: span, inputs: [ty::arg]) ->
   [TypeRef] {
    let atys = [];
    for arg in inputs {
        let arg_ty = arg.ty;
        // FIXME: would be nice to have a constraint on arg
        // that would obviate the need for this check
        check non_ty_var(cx, arg_ty);
        let llty = type_of_inner(cx, sp, arg_ty);
        atys += [arg.mode == ast::by_val ? llty : T_ptr(llty)];
    }
    ret atys;
}

fn native_fn_wrapper_type(cx: @crate_ctxt, sp: span, ty_param_count: uint,
                          x: ty::t) -> TypeRef {
    alt ty::struct(cx.tcx, x) {
      ty::ty_native_fn(args, out) {
        check non_ty_var(cx, out);
        ret type_of_fn(cx, sp, false, args, out, ty_param_count);
      }
    }
}

fn raw_native_fn_type(ccx: @crate_ctxt, sp: span, args: [ty::arg],
                      ret_ty: ty::t) -> TypeRef {
    check type_has_static_size(ccx, ret_ty);
    ret T_fn(type_of_explicit_args(ccx, sp, args), type_of(ccx, sp, ret_ty));
}

// NB: must keep 4 fns in sync:
//
//  - type_of_fn
//  - create_llargs_for_fn_args.
//  - new_fn_ctxt
//  - trans_args
fn type_of_fn(cx: @crate_ctxt, sp: span,
              is_method: bool, inputs: [ty::arg],
              output: ty::t, ty_param_count: uint)
   : non_ty_var(cx, output) -> TypeRef {
    let atys: [TypeRef] = [];

    // Arg 0: Output pointer.
    let out_ty = T_ptr(type_of_inner(cx, sp, output));
    atys += [out_ty];

    // Arg 1: Env (closure-bindings / self-obj)
    if is_method {
        atys += [T_ptr(cx.rust_object_type)];
    } else {
        atys += [T_opaque_boxed_closure_ptr(cx)];
    }

    // Args >2: ty params, if not acquired via capture...
    if !is_method {
        let i = 0u;
        while i < ty_param_count { atys += [T_ptr(cx.tydesc_type)]; i += 1u; }
    }
    // ... then explicit args.
    atys += type_of_explicit_args(cx, sp, inputs);
    ret T_fn(atys, llvm::LLVMVoidType());
}

// Given a function type and a count of ty params, construct an llvm type
fn type_of_fn_from_ty(cx: @crate_ctxt, sp: span, fty: ty::t,
                      ty_param_count: uint)
    : returns_non_ty_var(cx, fty) -> TypeRef {
    // FIXME: Check should be unnecessary, b/c it's implied
    // by returns_non_ty_var(t). Make that a postcondition
    // (see Issue #586)
    let ret_ty = ty::ty_fn_ret(cx.tcx, fty);
    check non_ty_var(cx, ret_ty);
    ret type_of_fn(cx, sp, false, ty::ty_fn_args(cx.tcx, fty),
                   ret_ty, ty_param_count);
}

fn type_of_inner(cx: @crate_ctxt, sp: span, t: ty::t)
    : non_ty_var(cx, t) -> TypeRef {
    // Check the cache.

    if cx.lltypes.contains_key(t) { ret cx.lltypes.get(t); }
    let llty = alt ty::struct(cx.tcx, t) {
      ty::ty_native(_) { T_ptr(T_i8()) }
      ty::ty_nil. { T_nil() }
      ty::ty_bot. { T_nil() /* ...I guess? */ }
      ty::ty_bool. { T_bool() }
      ty::ty_int(t) { T_int_ty(cx, t) }
      ty::ty_uint(t) { T_uint_ty(cx, t) }
      ty::ty_float(t) { T_float_ty(cx, t) }
      ty::ty_str. { T_ptr(T_vec(cx, T_i8())) }
      ty::ty_tag(did, tps) { type_of_tag(cx, sp, did, tps, t) }
      ty::ty_box(mt) {
        let mt_ty = mt.ty;
        check non_ty_var(cx, mt_ty);
        T_ptr(T_box(cx, type_of_inner(cx, sp, mt_ty))) }
      ty::ty_uniq(mt) {
        let mt_ty = mt.ty;
        check non_ty_var(cx, mt_ty);
        T_ptr(type_of_inner(cx, sp, mt_ty)) }
      ty::ty_vec(mt) {
        let mt_ty = mt.ty;
        if ty::type_has_dynamic_size(cx.tcx, mt_ty) {
            T_ptr(cx.opaque_vec_type)
        } else {
            // should be unnecessary
            check non_ty_var(cx, mt_ty);
            T_ptr(T_vec(cx, type_of_inner(cx, sp, mt_ty))) }
      }
      ty::ty_ptr(mt) {
        let mt_ty = mt.ty;
        check non_ty_var(cx, mt_ty);
        T_ptr(type_of_inner(cx, sp, mt_ty)) }
      ty::ty_rec(fields) {
        let tys: [TypeRef] = [];
        for f: ty::field in fields {
            let mt_ty = f.mt.ty;
            check non_ty_var(cx, mt_ty);
            tys += [type_of_inner(cx, sp, mt_ty)];
        }
        T_struct(tys)
      }
      ty::ty_fn(_, _, _, _, _) {
        // FIXME: could be a constraint on ty_fn
        check returns_non_ty_var(cx, t);
        T_fn_pair(cx, type_of_fn_from_ty(cx, sp, t, 0u))
      }
      ty::ty_native_fn(args, out) {
        let nft = native_fn_wrapper_type(cx, sp, 0u, t);
        T_fn_pair(cx, nft)
      }
      ty::ty_obj(meths) { cx.rust_object_type }
      ty::ty_res(_, sub, tps) {
        let sub1 = ty::substitute_type_params(cx.tcx, tps, sub);
        check non_ty_var(cx, sub1);
        // FIXME #1184: Resource flag is larger than necessary
        ret T_struct([cx.int_type, type_of_inner(cx, sp, sub1)]);
      }
      ty::ty_var(_) {
        // Should be unreachable b/c of precondition.
        // FIXME: would be nice to have a way of expressing this
        // through postconditions, and then making it sound to omit
        // cases in the alt
        std::util::unreachable()
      }
      ty::ty_param(_, _) { T_typaram(cx.tn) }
      ty::ty_send_type. | ty::ty_type. { T_ptr(cx.tydesc_type) }
      ty::ty_tup(elts) {
        let tys = [];
        for elt in elts {
            check non_ty_var(cx, elt);
            tys += [type_of_inner(cx, sp, elt)];
        }
        T_struct(tys)
      }
      ty::ty_opaque_closure. {
        T_opaque_closure(cx)
      }
      _ {
        log_err ("type_of_inner not implemented for ",
                ty::struct(cx.tcx, t));
        fail "type_of_inner not implemented for this kind of type";
      }
    };
    cx.lltypes.insert(t, llty);
    ret llty;
}

fn type_of_tag(ccx: @crate_ctxt, sp: span,
               did: ast::def_id, tps: [ty::t], t: ty::t)
    -> TypeRef {
    let tcx = ccx_tcx(ccx);

    assert type_has_static_size(ccx, t);

    // Creates a simpler, size-equivalent type. The resulting type is
    // guaranteed to have (a) the same size as the type that was
    // passed in; (b) to be non-recursive. This is done by replacing
    // all boxes in a type with boxed unit types.  This is necessary
    // since otherwise the type of a tag X where a variant included a
    // box @X would have infinite size (note: the tag itself would not
    // have infinite size, just the lltype representation).
    fn simplify_type(ccx: @crate_ctxt, typ: ty::t) -> ty::t {
        fn simplifier(ccx: @crate_ctxt, typ: ty::t) -> ty::t {
            fn imm_box(ccx: @crate_ctxt) -> ty::t {
                ret ty::mk_imm_box(ccx.tcx, ty::mk_nil(ccx.tcx));
            }
            alt ty::struct(ccx.tcx, typ) {
              ty::ty_box(_) { ret imm_box(ccx); }
              ty::ty_uniq(_) {
                ret ty::mk_imm_uniq(ccx.tcx, ty::mk_nil(ccx.tcx));
              }
              ty::ty_fn(_, _, _, _, _) {
                ret ty::mk_tup(ccx.tcx, [imm_box(ccx), imm_box(ccx)]);
              }
              ty::ty_obj(_) {
                ret ty::mk_tup(ccx.tcx, [imm_box(ccx), imm_box(ccx)]);
              }
              ty::ty_res(_, sub, tps) {
                let sub1 = ty::substitute_type_params(ccx.tcx, tps, sub);
                ret ty::mk_tup(ccx.tcx,
                               [ty::mk_int(ccx.tcx),
                                simplify_type(ccx, sub1)]);
              }
              _ { ret typ; }
            }
        }
        ret ty::fold_ty(ccx.tcx,
                        ty::fm_general(bind simplifier(ccx, _)),
                        typ);
    }

    let variants = ty::tag_variants(ccx.tcx, did);
    let llvariant_types = vec::map(*variants, { |variant|
        // Compute a non-recursive form of the type data.
        let tup_ty = ty::mk_tup(tcx, variant.args);
        let simp_ty = simplify_type(ccx, tup_ty);
        let subst_ty = ty::substitute_type_params(tcx, tps, simp_ty);
        if check type_has_static_size(ccx, subst_ty) {
            type_of(ccx, sp, subst_ty)
        } else {
            log_err(("t=", ty_to_str(ccx.tcx, t),
                     "tup_ty=", ty_to_str(ccx.tcx, tup_ty),
                     "simp_ty=", ty_to_str(ccx.tcx, simp_ty),
                     "subst_ty=", ty_to_str(ccx.tcx, subst_ty)));
            fail "type does not have static size";
        }
    });

    ret alt shape::tag_kind(ccx, did) {
      shape::tk_unit. {
        llvariant_types[0]
      }

      shape::tk_enum. {
        T_tag_variant(ccx)
      }

      shape::tk_complex. {
        // Find the max size/alignment of all variants, and
        // select the variant with largest alignment as a representative.
        let max_size = 0u, max_align = 0u, llrepr_ty = option::none;
        vec::iter(llvariant_types) { |llvariant_ty|
            let size = llsize_of_real(ccx, llvariant_ty);
            let align = llalign_of_real(ccx, llvariant_ty);

            // Find the variant with the largest alignment.
            if option::is_none(llrepr_ty) || align > max_align {
                llrepr_ty = option::some(llvariant_ty);
                max_align = align;
            }

            // Track largest size.
            max_size = uint::max(size, max_size);
        }

        // Pad the final size of the representative with extra
        // bytes if needed to make sure we leave enough space.
        let llrepr_ty = option::get(llrepr_ty);
        let size = llsize_of_real(ccx, llrepr_ty);
        if size < max_size {
            let pad = T_array(T_i8(), max_size - size);
            llrepr_ty = T_struct([llrepr_ty, pad]);
        }

        T_struct([T_tag_variant(ccx), llrepr_ty])
      }
    }
}

fn type_of_ty_param_kinds_and_ty(lcx: @local_ctxt, sp: span,
                                 tpt: ty::ty_param_kinds_and_ty) -> TypeRef {
    let cx = lcx.ccx;
    let t = tpt.ty;
    alt ty::struct(cx.tcx, t) {
      ty::ty_fn(_, _, _, _, _) | ty::ty_native_fn(_, _) {
        check returns_non_ty_var(cx, t);
        ret type_of_fn_from_ty(cx, sp, t, vec::len(tpt.kinds));
      }
      _ {
        // fall through
      }
    }
    // FIXME: could have a precondition on tpt, but that
    // doesn't work right now because one predicate can't imply
    // another
    check (type_has_static_size(cx, t));
    type_of(cx, sp, t)
}

fn type_of_or_i8(bcx: @block_ctxt, typ: ty::t) -> TypeRef {
    let ccx = bcx_ccx(bcx);
    if check type_has_static_size(ccx, typ) {
        let sp = bcx.sp;
        type_of(ccx, sp, typ)
    } else { T_i8() }
}

// ______________________________________________________________________


// Returns the real size of the given type for the current target.
fn llsize_of_real(cx: @crate_ctxt, t: TypeRef) -> uint {
    ret llvm::LLVMStoreSizeOfType(cx.td.lltd, t);
}

fn llsize_of(cx: @crate_ctxt, t: TypeRef) -> ValueRef {
    ret llvm::LLVMConstIntCast(lib::llvm::llvm::LLVMSizeOf(t), cx.int_type,
                               False);
}

// Returns the real alignment of the given type for the current target.
fn llalign_of_real(cx: @crate_ctxt, t: TypeRef) -> uint {
    ret llvm::LLVMPreferredAlignmentOfType(cx.td.lltd, t);
}

fn llalign_of(cx: @crate_ctxt, t: TypeRef) -> ValueRef {
    ret llvm::LLVMConstIntCast(lib::llvm::llvm::LLVMAlignOf(t), cx.int_type,
                               False);
}

fn size_of(bcx: @block_ctxt, t: ty::t) -> result {
    let ccx = bcx_ccx(bcx);
    if check type_has_static_size(ccx, t) {
        rslt(bcx, llsize_of(ccx, type_of(ccx, bcx.sp, t)))
    } else { dynamic_size_of(bcx, t) }
}

fn align_of(bcx: @block_ctxt, t: ty::t) -> result {
    let ccx = bcx_ccx(bcx);
    if check type_has_static_size(ccx, t) {
        rslt(bcx, llalign_of(ccx, type_of(ccx, bcx.sp, t)))
    } else { dynamic_align_of(bcx, t) }
}

fn blob_offset_of(_bcx: @block_ctxt,
                  _tag_id: ast::def_id,
                  _tps: [ty::t]) -> result {
    fail "TODO";
}

fn align_to(cx: @block_ctxt, off: ValueRef, align: ValueRef) -> ValueRef {
    let mask = Sub(cx, align, C_int(bcx_ccx(cx), 1));
    let bumped = Add(cx, off, mask);
    ret And(cx, bumped, Not(cx, mask));
}

fn umax(cx: @block_ctxt, a: ValueRef, b: ValueRef) -> ValueRef {
    let cond = ICmp(cx, lib::llvm::LLVMIntULT, a, b);
    ret Select(cx, cond, b, a);
}

fn umin(cx: @block_ctxt, a: ValueRef, b: ValueRef) -> ValueRef {
    let cond = ICmp(cx, lib::llvm::LLVMIntULT, a, b);
    ret Select(cx, cond, a, b);
}

type tag_metrics_result = {
    bcx: @block_ctxt,
    data_offset: ValueRef,
    total_size: ValueRef,
    total_align: ValueRef
};

fn compute_tag_metrics(bcx0: @block_ctxt,
                       tag_id: ast::def_id,
                       tag_tps: [ty::t]) -> tag_metrics_result {
    let bcx = bcx0;
    let ccx = bcx_ccx(bcx);
    let tcx = bcx_tcx(bcx);

    // Initialize variables we will use to store the max
    // data offset and size to 0.
    let max_size: ValueRef = trans::alloca(bcx, ccx.int_type);
    let max_align: ValueRef = trans::alloca(bcx, ccx.int_type);
    Store(bcx, C_int(ccx, 0), max_size);
    Store(bcx, C_int(ccx, 0), max_align);

    // We "want" a tag like  `tag { v1(t1[0]...t1[N]); v2(t2[0]...t2[N]); }`
    // like to expand into the equivalent of a C struct like:
    //
    //     struct {
    //         unsigned variant_id;
    //         union {
    //           struct { t1[0] ... t1[N] } data1;
    //           struct { t1[0] ... t1[N] } data2;
    //         } data;
    //     };
    //
    // n.b.: According to the C rules, the size and alignment of a union are
    // equal to the largest size and alignment of any variant.  Note that
    // the variant with the largest size may not have the largest alignment.

    fn update_max(bcx: @block_ctxt, max: ValueRef, cur: ValueRef) {
        let old_max = Load(bcx, max);
        Store(bcx, umax(bcx, cur, old_max), max);
    }

    // Compute the largest size/alignment of a variant:
    let variants = ty::tag_variants(tcx, tag_id);
    for variant: ty::variant_info in *variants {
        // Perform type substitution on the raw argument types.
        let raw_tys: [ty::t] = variant.args;
        let data_tys: [ty::t] = vec::map(raw_tys, { |raw_ty|
            ty::substitute_type_params(tcx, tag_tps, raw_ty)
        });
        let data_ty = ty::mk_tup(tcx, data_tys);
        let data_align = align_of(bcx, data_ty);
        bcx = data_align.bcx;
        let data_size = size_of(bcx, data_ty);
        bcx = data_size.bcx;
        update_max(bcx, max_size, data_size.val);
        update_max(bcx, max_align, data_align.val);
    }

    // Compute total size, alignment, and offset of data within the structure:
    ret alt shape::tag_kind(ccx, tag_id) {
      shape::tk_unit. {
        // No variant id.
        {bcx: bcx,
         data_offset: C_int(ccx, 0),
         total_size: Load(bcx, max_size),
         total_align: Load(bcx, max_align)}
      }
      shape::tk_enum. | shape::tk_complex. {
        // Variant id then data.  Compute total size/alignment of
        // a struct like: struct T { int variant_id; struct data { ... } };
        let variant_id_t = T_tag_variant(ccx);
        let variant_id_sizeof = llsize_of(ccx, variant_id_t);
        let variant_id_align = llalign_of(ccx, variant_id_t);
        let data_align = Load(bcx, max_align);
        let data_offset = align_to(bcx, variant_id_sizeof, data_align);
        let data_size = Load(bcx, max_size);
        let total_size = Add(bcx, data_offset, data_size);
        let total_align = umax(bcx, variant_id_align, data_align);
        {bcx: bcx,
         data_offset: data_offset,
         total_size: total_size,
         total_align: total_align}
      }
    };
}

fn dynamic_size_of(bcx: @block_ctxt, t: ty::t) -> result {
    fn align_elements(bcx0: @block_ctxt, elts: [ty::t]) -> result {
        //
        // C padding rules:
        //
        //
        //   - Pad after each element so that next element is aligned.
        //   - Pad after final structure member so that whole structure
        //     is aligned to max alignment of interior.
        //

        let bcx = bcx0;
        let off = C_int(bcx_ccx(bcx), 0);
        let max_align = C_int(bcx_ccx(bcx), 1);
        for e: ty::t in elts {
            let elt_align = align_of(bcx, e);
            bcx = elt_align.bcx;
            let elt_size = size_of(bcx, e);
            bcx = elt_size.bcx;
            let aligned_off = align_to(bcx, off, elt_align.val);
            off = Add(bcx, aligned_off, elt_size.val);
            max_align = umax(bcx, max_align, elt_align.val);
        }
        ret rslt(bcx, off);
    }

    alt ty::struct(bcx_tcx(bcx), t) {
      ty::ty_param(p, _) {
        let szptr =
            trans::field_of_tydesc(bcx, t, false, abi::tydesc_field_size);
        ret rslt(szptr.bcx, Load(szptr.bcx, szptr.val));
      }
      ty::ty_rec(flds) {
        let tys: [ty::t] = [];
        for f: ty::field in flds { tys += [f.mt.ty]; }
        ret align_elements(bcx, tys);
      }
      ty::ty_tup(elts) {
        let tys = [];
        for tp in elts { tys += [tp]; }
        ret align_elements(bcx, tys);
      }
      ty::ty_tag(tid, tps) {
        let metrics = compute_tag_metrics(bcx, tid, tps);
        ret {bcx: metrics.bcx, val: metrics.total_size};
      }
    }
}

fn dynamic_align_of(bcx: @block_ctxt, t: ty::t) -> result {
    // FIXME: Typestate constraint that shows this alt is
    // exhaustive
    alt ty::struct(bcx_tcx(bcx), t) {
      ty::ty_param(p, _) {
        let aptr =
            trans::field_of_tydesc(bcx, t, false, abi::tydesc_field_align);
        ret rslt(aptr.bcx, Load(aptr.bcx, aptr.val));
      }
      ty::ty_rec(flds) {
        let a = C_int(bcx_ccx(bcx), 1);
        let bcx = bcx;
        for f: ty::field in flds {
            let align = align_of(bcx, f.mt.ty);
            bcx = align.bcx;
            a = umax(bcx, a, align.val);
        }
        ret rslt(bcx, a);
      }
      ty::ty_tag(tid, tps) {
        let metrics = compute_tag_metrics(bcx, tid, tps);
        ret {bcx: metrics.bcx, val: metrics.total_align};
      }
      ty::ty_tup(elts) {
        let a = C_int(bcx_ccx(bcx), 1);
        let bcx = bcx;
        for e in elts {
            let align = align_of(bcx, e);
            bcx = align.bcx;
            a = umax(bcx, a, align.val);
        }
        ret rslt(bcx, a);
      }
    }
}

// Increment a pointer by a given amount and then cast it to be a pointer
// to a given type.
fn bump_ptr(bcx: @block_ctxt, t: ty::t, base: ValueRef, sz: ValueRef) ->
   ValueRef {
    let raw = PointerCast(bcx, base, T_ptr(T_i8()));
    let bumped = GEP(bcx, raw, [sz]);
    let ccx = bcx_ccx(bcx);
    if check type_has_static_size(ccx, t) {
        let sp = bcx.sp;
        let typ = T_ptr(type_of(ccx, sp, t));
        PointerCast(bcx, bumped, typ)
    } else { bumped }
}

// GEP_tup_like is a pain to use if you always have to precede it with a
// check.
fn GEP_tup_like_1(bcx: @block_ctxt, t: ty::t, base: ValueRef, ixs: [int])
    -> result {
    check type_is_tup_like(bcx, t);
    ret GEP_tup_like(bcx, t, base, ixs);
}

// Replacement for the LLVM 'GEP' instruction when field-indexing into a
// tuple-like structure (tup, rec) with a static index. This one is driven off
// ty::struct and knows what to do when it runs into a ty_param stuck in the
// middle of the thing it's GEP'ing into. Much like size_of and align_of,
// above.
fn GEP_tup_like(bcx0: @block_ctxt, t: ty::t, base: ValueRef, ixs: [int])
    : type_is_tup_like(bcx0, t) -> result {
    let bcx = bcx0;

    // It might be a static-known type. Handle this.
    if !ty::type_has_dynamic_size(bcx_tcx(bcx), t) {
        ret rslt(bcx, GEPi(bcx, base, ixs));
    }
    // It is a dynamic-containing type that, if we convert directly to an LLVM
    // TypeRef, will be all wrong; there's no proper LLVM type to represent
    // it, and the lowering function will stick in i8* values for each
    // ty_param, which is not right; the ty_params are all of some dynamic
    // size.
    //
    // What we must do instead is sadder. We must look through the indices
    // manually and split the input type into a prefix and a target. We then
    // measure the prefix size, bump the input pointer by that amount, and
    // cast to a pointer-to-target type.

    // Given a type, an index vector and an element number N in that vector,
    // calculate index X and the type that results by taking the first X-1
    // elements of the type and splitting the Xth off. Return the prefix as
    // well as the innermost Xth type.

    fn split_type(ccx: @crate_ctxt, t: ty::t, ixs: [int], n: uint) ->
       {prefix: [ty::t], target: ty::t} {
        let len: uint = vec::len::<int>(ixs);
        // We don't support 0-index or 1-index GEPs: The former is nonsense
        // and the latter would only be meaningful if we supported non-0
        // values for the 0th index (we don't).

        assert (len > 1u);
        if n == 0u {
            // Since we're starting from a value that's a pointer to a
            // *single* structure, the first index (in GEP-ese) should just be
            // 0, to yield the pointee.

            assert (ixs[n] == 0);
            ret split_type(ccx, t, ixs, n + 1u);
        }
        assert (n < len);
        let ix: int = ixs[n];
        let prefix: [ty::t] = [];
        let i: int = 0;
        while i < ix {
            prefix += [ty::get_element_type(ccx.tcx, t, i as uint)];
            i += 1;
        }
        let selected = ty::get_element_type(ccx.tcx, t, i as uint);
        if n == len - 1u {
            // We are at the innermost index.

            ret {prefix: prefix, target: selected};
        } else {
            // Not the innermost index; call self recursively to dig deeper.
            // Once we get an inner result, append it current prefix and
            // return to caller.

            let inner = split_type(ccx, selected, ixs, n + 1u);
            prefix += inner.prefix;
            ret {prefix: prefix with inner};
        }
    }
    // We make a fake prefix tuple-type here; luckily for measuring sizes
    // the tuple parens are associative so it doesn't matter that we've
    // flattened the incoming structure.

    let s = split_type(bcx_ccx(bcx), t, ixs, 0u);

    let args = [];
    for typ: ty::t in s.prefix { args += [typ]; }
    let prefix_ty = ty::mk_tup(bcx_tcx(bcx), args);

    let raw_sz = size_of(bcx, prefix_ty);
    bcx = raw_sz.bcx;
    let next_align = align_of(bcx, s.target);
    bcx = next_align.bcx;
    let sz = align_to(next_align.bcx, raw_sz.val, next_align.val);
    ret rslt(bcx, bump_ptr(bcx, s.target, base, sz));
}

/*

Note to self:

What is needed here-- this function takes an llblobptr, which is a
pointer to the data area of the tag. But this is bad, the caller
cannot know that offset, not really.  The function should take a
pointer to the tag value as a whole.  It must then compute the offset
of the data, which might be a dynamic value.  This is basically a
third metric, like sizeof() and alignof().  Otherwise the code can
more-or-less remain the same.

*/


// Replacement for the LLVM 'GEP' instruction when field indexing into a tag.
// This function uses GEP_tup_like() above and automatically performs casts as
// appropriate. @llblobptr is the data part of a tag value; its actual type is
// meaningless, as it will be cast away.
fn GEP_tag(bcx: @block_ctxt, lltagptr: ValueRef, tag_id: ast::def_id,
           variant_id: ast::def_id, ty_substs: [ty::t],
           ix: uint) : valid_variant_index(ix, bcx, tag_id, variant_id) ->
   result {
    let ccx = bcx_ccx(bcx);
    let tcx = bcx_tcx(bcx);

    // Compute offset and type of the blob and then create a ptr to it.
    let {bcx, val:bloboffs} = blob_offset_of(bcx, tag_id, ty_substs);
    let variant = ty::tag_variant_with_id(tcx, tag_id, variant_id);
    let true_arg_tys = vec::map(variant.args, { |aty|
        ty::substitute_type_params(tcx, ty_substs, aty)
    });
    let blob_ty = ty::mk_tup(tcx, true_arg_tys);
    let llblobptr = bump_ptr(bcx, blob_ty, lltagptr, bloboffs);

    // Get type of the element we are targeting.  Here ix must be valid.
    let elem_ty = true_arg_tys[ix];

    // Do the GEP_tup_like().
    let rs = GEP_tup_like_1(bcx, blob_ty, llblobptr, [0, ix as int]);

    // Cast the result to the appropriate type, if necessary.
    let rs_ccx = bcx_ccx(rs.bcx);
    let val =
        if check type_has_static_size(rs_ccx, elem_ty) {
            let llelemty = type_of(rs_ccx, bcx.sp, elem_ty);
            PointerCast(rs.bcx, rs.val, T_ptr(llelemty))
        } else { rs.val };

    ret rslt(rs.bcx, val);
}
