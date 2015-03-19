// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//!
//
// Code relating to taking, dropping, etc as well as type descriptors.


use back::abi;
use back::link::*;
use llvm::{ValueRef, True, get_param};
use llvm;
use middle::lang_items::ExchangeFreeFnLangItem;
use middle::subst;
use middle::subst::{Subst, Substs};
use trans::adt;
use trans::adt::GetDtorType; // for tcx.dtor_type()
use trans::base::*;
use trans::build::*;
use trans::callee;
use trans::cleanup;
use trans::cleanup::CleanupMethods;
use trans::consts;
use trans::common::*;
use trans::datum;
use trans::debuginfo::DebugLoc;
use trans::expr;
use trans::machine::*;
use trans::tvec;
use trans::type_::Type;
use trans::type_of::{self, type_of, sizing_type_of, align_of};
use middle::ty::{self, Ty};
use util::ppaux::{ty_to_short_str, Repr};
use util::ppaux;

use arena::TypedArena;
use libc::c_uint;
use session::config::NoDebugInfo;
use std::ffi::CString;
use syntax::ast;
use syntax::parse::token;

pub fn trans_exchange_free_dyn<'blk, 'tcx>(cx: Block<'blk, 'tcx>,
                                           v: ValueRef,
                                           size: ValueRef,
                                           align: ValueRef,
                                           debug_loc: DebugLoc)
                                           -> Block<'blk, 'tcx> {
    let _icx = push_ctxt("trans_exchange_free");
    let ccx = cx.ccx();
    callee::trans_lang_call(cx,
        langcall(cx, None, "", ExchangeFreeFnLangItem),
        &[PointerCast(cx, v, Type::i8p(ccx)), size, align],
        Some(expr::Ignore),
        debug_loc).bcx
}

pub fn trans_exchange_free<'blk, 'tcx>(cx: Block<'blk, 'tcx>,
                                       v: ValueRef,
                                       size: u64,
                                       align: u32,
                                       debug_loc: DebugLoc)
                                       -> Block<'blk, 'tcx> {
    trans_exchange_free_dyn(cx,
                            v,
                            C_uint(cx.ccx(), size),
                            C_uint(cx.ccx(), align),
                            debug_loc)
}

pub fn trans_exchange_free_ty<'blk, 'tcx>(bcx: Block<'blk, 'tcx>,
                                          ptr: ValueRef,
                                          content_ty: Ty<'tcx>,
                                          debug_loc: DebugLoc)
                                          -> Block<'blk, 'tcx> {
    assert!(type_is_sized(bcx.ccx().tcx(), content_ty));
    let sizing_type = sizing_type_of(bcx.ccx(), content_ty);
    let content_size = llsize_of_alloc(bcx.ccx(), sizing_type);

    // `Box<ZeroSizeType>` does not allocate.
    if content_size != 0 {
        let content_align = align_of(bcx.ccx(), content_ty);
        trans_exchange_free(bcx, ptr, content_size, content_align, debug_loc)
    } else {
        bcx
    }
}

pub fn get_drop_glue_type<'a, 'tcx>(ccx: &CrateContext<'a, 'tcx>,
                                    t: Ty<'tcx>) -> Ty<'tcx> {
    let tcx = ccx.tcx();
    // Even if there is no dtor for t, there might be one deeper down and we
    // might need to pass in the vtable ptr.
    if !type_is_sized(tcx, t) {
        return t
    }

    // FIXME (#22815): note that type_needs_drop conservatively
    // approximates in some cases and may say a type expression
    // requires drop glue when it actually does not.
    //
    // (In this case it is not clear whether any harm is done, i.e.
    // erroneously returning `t` in some cases where we could have
    // returned `tcx.types.i8` does not appear unsound. The impact on
    // code quality is unknown at this time.)

    if !type_needs_drop(tcx, t) {
        return tcx.types.i8;
    }
    match t.sty {
        ty::ty_uniq(typ) if !type_needs_drop(tcx, typ)
                         && type_is_sized(tcx, typ) => {
            let llty = sizing_type_of(ccx, typ);
            // `Box<ZeroSizeType>` does not allocate.
            if llsize_of_alloc(ccx, llty) == 0 {
                tcx.types.i8
            } else {
                t
            }
        }
        _ => t
    }
}

pub fn drop_ty<'blk, 'tcx>(bcx: Block<'blk, 'tcx>,
                           v: ValueRef,
                           t: Ty<'tcx>,
                           debug_loc: DebugLoc)
                           -> Block<'blk, 'tcx>
{
    debug!("drop_ty(t={})", t.repr(bcx.tcx()));
    let _icx = push_ctxt("drop_ty");
    drop_ty_core(bcx, v, t, debug_loc, DropGlueKind::Drop)
}

pub fn forget_ty<'blk, 'tcx>(bcx: Block<'blk, 'tcx>,
                             v: ValueRef,
                             t: Ty<'tcx>,
                             debug_loc: DebugLoc)
                             -> Block<'blk, 'tcx>
{
    debug!("forget_ty(t={})", t.repr(bcx.tcx()));
    let _icx = push_ctxt("forget_ty");
    drop_ty_core(bcx, v, t, debug_loc, DropGlueKind::Forget)
}

fn drop_ty_core<'blk, 'tcx>(bcx: Block<'blk, 'tcx>,
                            v: ValueRef,
                            t: Ty<'tcx>,
                            debug_loc: DebugLoc,
                            kind: DropGlueKind)
                            -> Block<'blk, 'tcx> {
    // NB: v is an *alias* of type t here, not a direct value.
    if bcx.fcx.type_needs_drop(t) {
        let ccx = bcx.ccx();
        let glue = get_drop_glue(ccx, t, kind);
        let glue_type = get_drop_glue_type(ccx, t);
        let ptr = if glue_type != t {
            PointerCast(bcx, v, type_of(ccx, glue_type).ptr_to())
        } else {
            v
        };

        Call(bcx, glue, &[ptr], None, debug_loc);
    }
    bcx
}

pub fn drop_ty_immediate<'blk, 'tcx>(bcx: Block<'blk, 'tcx>,
                                     v: ValueRef,
                                     t: Ty<'tcx>,
                                     debug_loc: DebugLoc)
                                     -> Block<'blk, 'tcx> {
    let _icx = push_ctxt("drop_ty_immediate");
    let vp = alloca(bcx, type_of(bcx.ccx(), t), "");
    store_ty(bcx, v, vp, t);
    drop_ty(bcx, vp, t, debug_loc)
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DropGlueKind {
    Drop,
    Forget,
}

pub fn get_drop_glue<'a, 'tcx>(ccx: &CrateContext<'a, 'tcx>, t: Ty<'tcx>, kind: DropGlueKind) -> ValueRef {
    debug!("make drop glue for {} kind: {:?}", ppaux::ty_to_string(ccx.tcx(), t), kind);
    let t = get_drop_glue_type(ccx, t);
    let name = match kind {
        DropGlueKind::Drop => "drop",
        DropGlueKind::Forget => "forget",
    };
    debug!("{} glue type {}", name, ppaux::ty_to_string(ccx.tcx(), t));
    match ccx.drop_glues(kind).borrow().get(&t) {
        Some(&glue) => return glue,
        _ => { }
    }

    let llty = if type_is_sized(ccx.tcx(), t) {
        type_of(ccx, t).ptr_to()
    } else {
        type_of(ccx, ty::mk_uniq(ccx.tcx(), t)).ptr_to()
    };

    let llfnty = Type::glue_fn(ccx, llty);

    let (glue, new_sym) = match ccx.available_drop_glues(kind).borrow().get(&t) {
        Some(old_sym) => {
            let glue = decl_cdecl_fn(ccx, &old_sym[..], llfnty, ty::mk_nil(ccx.tcx()));
            (glue, None)
        },
        None => {
            let (sym, glue) = declare_generic_glue(ccx, t, llfnty, name);
            (glue, Some(sym))
        },
    };

    ccx.drop_glues(kind).borrow_mut().insert(t, glue);

    // To avoid infinite recursion, don't `make_drop_glue` until after we've
    // added the entry to the `drop_glues` cache.
    match new_sym {
        Some(sym) => {
            ccx.available_drop_glues(kind).borrow_mut().insert(t, sym);
            // We're creating a new drop glue, so also generate a body.
            match kind {
                DropGlueKind::Drop => {
                    make_generic_glue(ccx, t, glue, make_drop_glue, name);
                }
                DropGlueKind::Forget => {
                    make_generic_glue(ccx, t, glue, make_forget_glue, name);
                }
            };
        },
        None => {},
    }

    glue
}

fn trans_struct_drop_flag<'blk, 'tcx>(mut bcx: Block<'blk, 'tcx>,
                                      t: Ty<'tcx>,
                                      v0: ValueRef,
                                      dtor_did: ast::DefId,
                                      class_did: ast::DefId,
                                      substs: &subst::Substs<'tcx>)
                                      -> Block<'blk, 'tcx> {
    let repr = adt::represent_type(bcx.ccx(), t);
    let struct_data = if type_is_sized(bcx.tcx(), t) {
        v0
    } else {
        let llval = GEPi(bcx, v0, &[0, abi::FAT_PTR_ADDR]);
        Load(bcx, llval)
    };
    let drop_flag = unpack_datum!(bcx, adt::trans_drop_flag_ptr(bcx, &*repr, struct_data));
    let loaded = load_ty(bcx, drop_flag.val, bcx.tcx().dtor_type());
    // FIXME (pnkfelix): need to properly map bcx.tcx().dtor_type() to int type below.
    let init_val = C_integral(Type::i8(bcx.fcx.ccx), adt::DTOR_NEEDED as u64, false);

    let bcx = if bcx.tcx().sess.opts.debuginfo == NoDebugInfo {
        bcx
    } else {
        // FIXME (pnkfelix): need to properly map bcx.tcx().dtor_type() to int type below.
        let done_val = C_integral(Type::i8(bcx.fcx.ccx), adt::DTOR_DONE as u64, false);
        let not_init = ICmp(bcx, llvm::IntNE, loaded, init_val, DebugLoc::None);
        let not_done = ICmp(bcx, llvm::IntNE, loaded, done_val, DebugLoc::None);
        let drop_flag_neither_initialized_nor_cleared =
            And(bcx, not_init, not_done, DebugLoc::None);
        with_cond(bcx, drop_flag_neither_initialized_nor_cleared, |cx| {
            let llfn = cx.ccx().get_intrinsic(&("llvm.debugtrap"));
            Call(cx, llfn, &[], None, DebugLoc::None);
            cx
        })
    };

    let drop_flag_dtor_needed = ICmp(bcx, llvm::IntEQ, loaded, init_val, DebugLoc::None);
    with_cond(bcx, drop_flag_dtor_needed, |cx| {
        trans_struct_drop(cx, t, v0, dtor_did, class_did, substs)
    })

}

fn trans_struct_drop<'blk, 'tcx>(bcx: Block<'blk, 'tcx>,
                                 t: Ty<'tcx>,
                                 v0: ValueRef,
                                 dtor_did: ast::DefId,
                                 class_did: ast::DefId,
                                 substs: &subst::Substs<'tcx>)
                                 -> Block<'blk, 'tcx>
{
    trans_struct_drop_core(
        bcx, t, v0, dtor_did, class_did, substs, DropGlueKind::Drop)
}

fn trans_struct_forget<'blk, 'tcx>(bcx: Block<'blk, 'tcx>,
                                   t: Ty<'tcx>,
                                   v0: ValueRef,
                                   forgetter_did: ast::DefId,
                                   class_did: ast::DefId,
                                   substs: &subst::Substs<'tcx>)
                                   -> Block<'blk, 'tcx>
{
    debug!("trans_struct_forget t: {} forgetter_did: {} class_did: {}",
           t.repr(bcx.tcx()),
           forgetter_did.repr(bcx.tcx()),
           class_did.repr(bcx.tcx()));
    trans_struct_drop_core(
        bcx, t, v0, forgetter_did, class_did, substs, DropGlueKind::Forget)
}

fn trans_struct_drop_core<'blk, 'tcx>(bcx: Block<'blk, 'tcx>,
                                      t: Ty<'tcx>,
                                      v0: ValueRef,
                                      dtor_did: ast::DefId,
                                      class_did: ast::DefId,
                                      substs: &subst::Substs<'tcx>,
                                      _kind: DropGlueKind)
                                      -> Block<'blk, 'tcx>
{
    let repr = adt::represent_type(bcx.ccx(), t);

    // Find and call the actual destructor
    let dtor_addr = get_res_dtor(bcx.ccx(), dtor_did, t,
                                 class_did, substs);

    // The first argument is the "self" argument for drop
    let params = unsafe {
        let ty = Type::from_ref(llvm::LLVMTypeOf(dtor_addr));
        ty.element_type().func_params()
    };

    let fty = ty::lookup_item_type(bcx.tcx(), dtor_did).ty.subst(bcx.tcx(), substs);
    let self_ty = match fty.sty {
        ty::ty_bare_fn(_, ref f) => {
            let sig = ty::erase_late_bound_regions(bcx.tcx(), &f.sig);
            assert!(sig.inputs.len() == 1);
            sig.inputs[0]
        }
        _ => bcx.sess().bug(&format!("Expected function type, found {}",
                                    bcx.ty_to_string(fty)))
    };

    let (struct_data, info) = if type_is_sized(bcx.tcx(), t) {
        (v0, None)
    } else {
        let data = GEPi(bcx, v0, &[0, abi::FAT_PTR_ADDR]);
        let info = GEPi(bcx, v0, &[0, abi::FAT_PTR_EXTRA]);
        (Load(bcx, data), Some(Load(bcx, info)))
    };

    adt::fold_variants(bcx, &*repr, struct_data, |variant_cx, st, value| {
        // Be sure to put all of the fields into a scope so we can use an invoke
        // instruction to call the user destructor but still call the field
        // destructors if the user destructor panics.
        let field_scope = variant_cx.fcx.push_custom_cleanup_scope();

        // Class dtors have no explicit args, so the params should
        // just consist of the environment (self).
        assert_eq!(params.len(), 1);
        let self_arg = if type_is_fat_ptr(bcx.tcx(), self_ty) {
            // The dtor expects a fat pointer, so make one, even if we have to fake it.
            let scratch = datum::rvalue_scratch_datum(bcx, t, "__fat_ptr_drop_self");
            Store(bcx, value, GEPi(bcx, scratch.val, &[0, abi::FAT_PTR_ADDR]));
            Store(bcx,
                  // If we just had a thin pointer, make a fat pointer by sticking
                  // null where we put the unsizing info. This works because t
                  // is a sized type, so we will only unpack the fat pointer, never
                  // use the fake info.
                  info.unwrap_or(C_null(Type::i8p(bcx.ccx()))),
                  GEPi(bcx, scratch.val, &[0, abi::FAT_PTR_EXTRA]));
            PointerCast(variant_cx, scratch.val, params[0])
        } else {
            PointerCast(variant_cx, value, params[0])
        };
        let args = vec!(self_arg);

        // Add all the fields as a value which needs to be cleaned at the end of
        // this scope. Iterate in reverse order so a Drop impl doesn't reverse
        // the order in which fields get dropped.
        for (i, &ty) in st.fields.iter().enumerate().rev() {
            let llfld_a = adt::struct_field_ptr(variant_cx, &*st, value, i, false);

            let val = if type_is_sized(bcx.tcx(), ty) {
                llfld_a
            } else {
                let scratch = datum::rvalue_scratch_datum(bcx, ty, "__fat_ptr_drop_field");
                Store(bcx, llfld_a, GEPi(bcx, scratch.val, &[0, abi::FAT_PTR_ADDR]));
                Store(bcx, info.unwrap(), GEPi(bcx, scratch.val, &[0, abi::FAT_PTR_EXTRA]));
                scratch.val
            };
            variant_cx.fcx.schedule_drop_mem(cleanup::CustomScope(field_scope), val, ty);
        }

        let dtor_ty = ty::mk_ctor_fn(bcx.tcx(),
                                     class_did,
                                     &[get_drop_glue_type(bcx.ccx(), t)],
                                     ty::mk_nil(bcx.tcx()));
        let (_, variant_cx) = invoke(variant_cx, dtor_addr, &args[..], dtor_ty, DebugLoc::None);

        variant_cx.fcx.pop_and_trans_custom_cleanup_scope(variant_cx, field_scope)
    })
}

fn size_and_align_of_dst<'blk, 'tcx>(bcx: Block<'blk, 'tcx>, t: Ty<'tcx>, info: ValueRef)
                                     -> (ValueRef, ValueRef) {
    debug!("calculate size of DST: {}; with lost info: {}",
           bcx.ty_to_string(t), bcx.val_to_string(info));
    if type_is_sized(bcx.tcx(), t) {
        let sizing_type = sizing_type_of(bcx.ccx(), t);
        let size = C_uint(bcx.ccx(), llsize_of_alloc(bcx.ccx(), sizing_type));
        let align = C_uint(bcx.ccx(), align_of(bcx.ccx(), t));
        return (size, align);
    }
    match t.sty {
        ty::ty_struct(id, substs) => {
            let ccx = bcx.ccx();
            // First get the size of all statically known fields.
            // Don't use type_of::sizing_type_of because that expects t to be sized.
            assert!(!ty::type_is_simd(bcx.tcx(), t));
            let repr = adt::represent_type(ccx, t);
            let sizing_type = adt::sizing_type_of(ccx, &*repr, true);
            let sized_size = C_uint(ccx, llsize_of_alloc(ccx, sizing_type));
            let sized_align = C_uint(ccx, llalign_of_min(ccx, sizing_type));

            // Recurse to get the size of the dynamically sized field (must be
            // the last field).
            let fields = ty::struct_fields(bcx.tcx(), id, substs);
            let last_field = fields[fields.len()-1];
            let field_ty = last_field.mt.ty;
            let (unsized_size, unsized_align) = size_and_align_of_dst(bcx, field_ty, info);

            // Return the sum of sizes and max of aligns.
            let size = Add(bcx, sized_size, unsized_size, DebugLoc::None);
            let align = Select(bcx,
                               ICmp(bcx,
                                    llvm::IntULT,
                                    sized_align,
                                    unsized_align,
                                    DebugLoc::None),
                               sized_align,
                               unsized_align);
            (size, align)
        }
        ty::ty_trait(..) => {
            // info points to the vtable and the second entry in the vtable is the
            // dynamic size of the object.
            let info = PointerCast(bcx, info, Type::int(bcx.ccx()).ptr_to());
            let size_ptr = GEPi(bcx, info, &[1]);
            let align_ptr = GEPi(bcx, info, &[2]);
            (Load(bcx, size_ptr), Load(bcx, align_ptr))
        }
        ty::ty_vec(_, None) | ty::ty_str => {
            let unit_ty = ty::sequence_element_type(bcx.tcx(), t);
            // The info in this case is the length of the str, so the size is that
            // times the unit size.
            let llunit_ty = sizing_type_of(bcx.ccx(), unit_ty);
            let unit_align = llalign_of_min(bcx.ccx(), llunit_ty);
            let unit_size = llsize_of_alloc(bcx.ccx(), llunit_ty);
            (Mul(bcx, info, C_uint(bcx.ccx(), unit_size), DebugLoc::None),
             C_uint(bcx.ccx(), unit_align))
        }
        _ => bcx.sess().bug(&format!("Unexpected unsized type, found {}",
                                    bcx.ty_to_string(t)))
    }
}

fn make_forget_glue<'blk, 'tcx>(bcx: Block<'blk, 'tcx>,
                                v0: ValueRef,
                                t: Ty<'tcx>)
                                -> Block<'blk, 'tcx>
{
    // NB: v0 is an *alias* of type t here, not a direct value.
    let _icx = push_ctxt("make_forget_glue");
    match t.sty {
        ty::ty_struct(did, substs) | ty::ty_enum(did, substs) => {
            let tcx = bcx.tcx();
            match ty::ty_dtor(tcx, did) {
                ty::TraitDtor { forgetter_did: Some(forgetter), .. } => {
                    trans_struct_forget(bcx, t, v0, forgetter, did, substs)
                }

                ty::TraitDtor { forgetter_did: None, .. } |
                ty::NoDtor => {
                    // No destructor or forgetter? Just the default case
                    iter_structural_ty(bcx, v0, t,
                                       |bb, vv, tt| forget_ty(bb, vv, tt, DebugLoc::None))
                }
            }
        }

        // TODO FIXME
        #[cfg(not_now_fsk_thinks_this_is_subsumed_below)]
        ty::ty_closure(..) => {
            iter_structural_ty(bcx,
                               v0,
                               t,
                               |bb, vv, tt| forget_ty(bb, vv, tt, DebugLoc::None))
        }

        ty::ty_trait(..) | ty::ty_vec(_, None) | ty::ty_str => {
            // no forget glue necessary for these cases
            bcx
        }

        _ if bcx.fcx.type_needs_drop(t) && ty::type_is_structural(t) => {
            assert!(type_is_sized(bcx.tcx(), t));
            iter_structural_ty(bcx,
                               v0,
                               t,
                               |bb, vv, tt| forget_ty(bb, vv, tt, DebugLoc::None))
        }

        _ => bcx,
    }
}


fn make_drop_glue<'blk, 'tcx>(bcx: Block<'blk, 'tcx>, v0: ValueRef, t: Ty<'tcx>)
                              -> Block<'blk, 'tcx> {
    // NB: v0 is an *alias* of type t here, not a direct value.
    let _icx = push_ctxt("make_drop_glue");

    // Only drop the value when it ... well, we used
    // to check for non-null, (and maybe we need to
    // continue doing so), but we now must definitely
    // check for special bit-patterns corresponding to
    // the special dtor markings.

    // let dropped_pattern = C_integral(bcx.fcx.ccx.int_type(),
    //                                  adt::dtor_done_usize(bcx.fcx.ccx) as u64,
    //                                  false);
    let inttype = Type::int(bcx.ccx());
    let dropped_pattern = C_integral(
        inttype, adt::dtor_done_usize(bcx.fcx.ccx) as u64, false);

    match t.sty {
        ty::ty_uniq(content_ty) => {
            match content_ty.sty {
                ty::ty_vec(ty, None) => {
                    debug!("make_drop_glue ty_uniq(ty_vec)");
                    tvec::make_drop_glue_unboxed(bcx, v0, ty, true)
                }
                ty::ty_str => {
                    debug!("make_drop_glue ty_uniq(ty_str)");
                    let unit_ty = ty::sequence_element_type(bcx.tcx(), content_ty);
                    tvec::make_drop_glue_unboxed(bcx, v0, unit_ty, true)
                }
                ty::ty_trait(..) => {
                    debug!("make_drop_glue ty_uniq(ty_trait)");
                    let lluniquevalue = GEPi(bcx, v0, &[0, abi::FAT_PTR_ADDR]);

                    let concrete_ptr = Load(bcx, lluniquevalue);
                    let concrete_ptr_as_usize = PtrToInt(bcx, concrete_ptr, Type::int(bcx.ccx()));
                    let drop_flag_not_dropped_already =
                        ICmp(bcx, llvm::IntNE, concrete_ptr_as_usize, dropped_pattern,
                             DebugLoc::None);

                    with_cond(bcx, drop_flag_not_dropped_already, |bcx| {
                        let dtor_ptr = Load(bcx, GEPi(bcx, v0, &[0, abi::FAT_PTR_EXTRA]));
                        let dtor = Load(bcx, dtor_ptr);
                        Call(bcx,
                             dtor,
                             &[PointerCast(bcx, lluniquevalue, Type::i8p(bcx.ccx()))],
                             None,
                             DebugLoc::None);
                        bcx
                    })
                }
                ty::ty_struct(..) if !type_is_sized(bcx.tcx(), content_ty) => {
                    debug!("make_drop_glue ty_uniq(ty_struct)");
                    let llval = GEPi(bcx, v0, &[0, abi::FAT_PTR_ADDR]);
                    let llbox = Load(bcx, llval);
                    let llbox_as_usize = PtrToInt(bcx, llbox, Type::int(bcx.ccx()));
                    let drop_flag_not_dropped_already =
                        ICmp(bcx, llvm::IntNE, llbox_as_usize, dropped_pattern, DebugLoc::None);
                    with_cond(bcx, drop_flag_not_dropped_already, |bcx| {
                        let bcx = drop_ty(bcx, v0, content_ty, DebugLoc::None);
                        let info = GEPi(bcx, v0, &[0, abi::FAT_PTR_EXTRA]);
                        let info = Load(bcx, info);
                        let (llsize, llalign) = size_and_align_of_dst(bcx, content_ty, info);
                        trans_exchange_free_dyn(bcx, llbox, llsize, llalign, DebugLoc::None)
                    })
                }
                _ => {
                    debug!("make_drop_glue ty_uniq(_other): {}", content_ty.repr(bcx.tcx()));
                    assert!(type_is_sized(bcx.tcx(), content_ty));
                    let llval = v0;
                    let llbox = Load(bcx, llval);

                    // FIXME: should not be playing guessing games about the type to use.
                    // let lltype = Type::from_ref(unsafe { llvm::LLVMTypeOf(llbox) });
                    // let inttype = Type::int(bcx.ccx());
                    // debug!("make_drop_glue ty_uniq(_other): cast {} as {}",
                    //        bcx.ccx().tn().type_to_string(lltype),
                    //        bcx.ccx().tn().type_to_string(inttype));
                    let llbox_as_usize = PtrToInt(bcx, llbox, inttype);
                    debug!("make_drop_glue ty_uniq(_other): successful ptrtoint cxn");
                    // let dropped_pattern = C_integral(
                    //     inttype, adt::dtor_done_usize(bcx.fcx.ccx) as u64, false);

                    let drop_flag_not_dropped_already =
                        ICmp(bcx, llvm::IntNE, llbox_as_usize, dropped_pattern, DebugLoc::None);
                    with_cond(bcx, drop_flag_not_dropped_already, |bcx| {
                        let bcx = drop_ty(bcx, llbox, content_ty, DebugLoc::None);
                        trans_exchange_free_ty(bcx, llbox, content_ty, DebugLoc::None)
                    })
                }
            }
        }
        ty::ty_struct(did, substs) | ty::ty_enum(did, substs) => {
            let tcx = bcx.tcx();
            match ty::ty_dtor(tcx, did) {
                ty::TraitDtor { dtor_did: dtor, has_drop_flag: true, .. } => {
                    // FIXME(16758) Since the struct is unsized, it is hard to
                    // find the drop flag (which is at the end of the struct).
                    // Lets just ignore the flag and pretend everything will be
                    // OK.
                    if type_is_sized(bcx.tcx(), t) {
                        trans_struct_drop_flag(bcx, t, v0, dtor, did, substs)
                    } else {
                        // Give the user a heads up that we are doing something
                        // stupid and dangerous.
                        bcx.sess().warn(&format!("Ignoring drop flag in destructor for {}\
                                                 because the struct is unsized. See issue\
                                                 #16758",
                                                bcx.ty_to_string(t)));
                        trans_struct_drop(bcx, t, v0, dtor, did, substs)
                    }
                }
                ty::TraitDtor { dtor_did: dtor, has_drop_flag: false, .. } => {
                    trans_struct_drop(bcx, t, v0, dtor, did, substs)
                }
                ty::NoDtor => {
                    // No dtor? Just the default case
                    iter_structural_ty(bcx, v0, t, |bb, vv, tt| drop_ty(bb, vv, tt, DebugLoc::None))
                }
            }
        }
        ty::ty_closure(..) => {
            iter_structural_ty(bcx,
                               v0,
                               t,
                               |bb, vv, tt| drop_ty(bb, vv, tt, DebugLoc::None))
        }
        ty::ty_trait(..) => {
            // No need to do a null check here (as opposed to the Box<trait case
            // above), because this happens for a trait field in an unsized
            // struct. If anything is null, it is the whole struct and we won't
            // get here.
            let lluniquevalue = GEPi(bcx, v0, &[0, abi::FAT_PTR_ADDR]);
            let dtor_ptr = Load(bcx, GEPi(bcx, v0, &[0, abi::FAT_PTR_EXTRA]));
            let dtor = Load(bcx, dtor_ptr);
            Call(bcx,
                 dtor,
                 &[PointerCast(bcx, Load(bcx, lluniquevalue), Type::i8p(bcx.ccx()))],
                 None,
                 DebugLoc::None);
            bcx
        },
        ty::ty_vec(_, None) | ty::ty_str => {
            let unit_ty = ty::sequence_element_type(bcx.tcx(), t);
            tvec::make_drop_glue_unboxed(bcx, v0, unit_ty, false)
        },
        _ => {
            assert!(type_is_sized(bcx.tcx(), t));
            if bcx.fcx.type_needs_drop(t) && ty::type_is_structural(t) {
                iter_structural_ty(bcx,
                                   v0,
                                   t,
                                   |bb, vv, tt| drop_ty(bb, vv, tt, DebugLoc::None))
            } else {
                bcx
            }
        }
    }
}

// Generates the declaration for (but doesn't emit) a type descriptor.
pub fn declare_tydesc<'a, 'tcx>(ccx: &CrateContext<'a, 'tcx>, t: Ty<'tcx>)
                                -> tydesc_info<'tcx> {
    // If emit_tydescs already ran, then we shouldn't be creating any new
    // tydescs.
    assert!(!ccx.finished_tydescs().get());

    // This really shouldn't be like this, size/align will be wrong for
    // unsized types (i.e. [T] will have the size/align of T).
    // But we need it until we split this out into a "type name" intrinsic.
    let llty = type_of::in_memory_type_of(ccx, t);

    if ccx.sess().count_type_sizes() {
        println!("{}\t{}", llsize_of_real(ccx, llty),
                 ppaux::ty_to_string(ccx.tcx(), t));
    }

    let llsize = llsize_of(ccx, llty);
    let llalign = llalign_of(ccx, llty);
    let name = mangle_internal_name_by_type_and_seq(ccx, t, "tydesc");
    debug!("+++ declare_tydesc {} {}", ppaux::ty_to_string(ccx.tcx(), t), name);
    let buf = CString::new(name.clone()).unwrap();
    let gvar = unsafe {
        llvm::LLVMAddGlobal(ccx.llmod(), ccx.tydesc_type().to_ref(),
                            buf.as_ptr())
    };
    note_unique_llvm_symbol(ccx, name);

    let ty_name = token::intern_and_get_ident(
        &ppaux::ty_to_string(ccx.tcx(), t));
    let ty_name = C_str_slice(ccx, ty_name);

    debug!("--- declare_tydesc {}", ppaux::ty_to_string(ccx.tcx(), t));
    tydesc_info {
        ty: t,
        tydesc: gvar,
        size: llsize,
        align: llalign,
        name: ty_name,
    }
}

fn declare_generic_glue<'a, 'tcx>(ccx: &CrateContext<'a, 'tcx>, t: Ty<'tcx>,
                                  llfnty: Type, name: &str) -> (String, ValueRef) {
    let _icx = push_ctxt("declare_generic_glue");
    let fn_nm = mangle_internal_name_by_type_and_seq(
        ccx,
        t,
        &format!("glue_{}", name));
    let llfn = decl_cdecl_fn(ccx, &fn_nm[..], llfnty, ty::mk_nil(ccx.tcx()));
    note_unique_llvm_symbol(ccx, fn_nm.clone());
    return (fn_nm, llfn);
}

fn make_generic_glue<'a, 'tcx, F>(ccx: &CrateContext<'a, 'tcx>,
                                  t: Ty<'tcx>,
                                  llfn: ValueRef,
                                  helper: F,
                                  name: &str)
                                  -> ValueRef where
    F: for<'blk> FnOnce(Block<'blk, 'tcx>, ValueRef, Ty<'tcx>) -> Block<'blk, 'tcx>,
{
    let _icx = push_ctxt("make_generic_glue");
    let glue_name = format!("glue {} {}", name, ty_to_short_str(ccx.tcx(), t));
    let _s = StatRecorder::new(ccx, glue_name);

    let empty_substs = ccx.tcx().mk_substs(Substs::trans_empty());
    let (arena, fcx): (TypedArena<_>, FunctionContext);
    arena = TypedArena::new();
    fcx = new_fn_ctxt(ccx, llfn, ast::DUMMY_NODE_ID, false,
                      ty::FnConverging(ty::mk_nil(ccx.tcx())),
                      empty_substs, None, &arena);

    let bcx = init_function(&fcx, false, ty::FnConverging(ty::mk_nil(ccx.tcx())));

    update_linkage(ccx, llfn, None, OriginalTranslation);

    ccx.stats().n_glues_created.set(ccx.stats().n_glues_created.get() + 1);
    // All glue functions take values passed *by alias*; this is a
    // requirement since in many contexts glue is invoked indirectly and
    // the caller has no idea if it's dealing with something that can be
    // passed by value.
    //
    // llfn is expected be declared to take a parameter of the appropriate
    // type, so we don't need to explicitly cast the function parameter.

    let llrawptr0 = get_param(llfn, fcx.arg_pos(0) as c_uint);
    let bcx = helper(bcx, llrawptr0, t);
    finish_fn(&fcx, bcx, ty::FnConverging(ty::mk_nil(ccx.tcx())), DebugLoc::None);

    llfn
}

pub fn emit_tydescs(ccx: &CrateContext) {
    let _icx = push_ctxt("emit_tydescs");
    // As of this point, allow no more tydescs to be created.
    ccx.finished_tydescs().set(true);
    let glue_fn_ty = Type::generic_glue_fn(ccx).ptr_to();
    for (_, ti) in &*ccx.tydescs().borrow() {
        // Each of the glue functions needs to be cast to a generic type
        // before being put into the tydesc because we only have a singleton
        // tydesc type. Then we'll recast each function to its real type when
        // calling it.
        let drop_glue = consts::ptrcast(get_drop_glue(ccx, ti.ty, DropGlueKind::Drop),
                                        glue_fn_ty);
        ccx.stats().n_real_glues.set(ccx.stats().n_real_glues.get() + 1);

        let tydesc = C_named_struct(ccx.tydesc_type(),
                                    &[ti.size, // size
                                      ti.align, // align
                                      drop_glue, // drop_glue
                                      ti.name]); // name

        unsafe {
            let gvar = ti.tydesc;
            llvm::LLVMSetInitializer(gvar, tydesc);
            llvm::LLVMSetGlobalConstant(gvar, True);
            llvm::SetLinkage(gvar, llvm::InternalLinkage);
        }
    };
}
