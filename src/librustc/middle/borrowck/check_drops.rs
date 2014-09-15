// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(unused_imports)]
#![allow(unused_variable)]

use metadata::csearch;
use middle::borrowck::*;
use middle::borrowck::move_data::{Assignment, Move};
use middle::expr_use_visitor as euv;
use lint;
use middle::mem_categorization as mc;
use middle::dataflow;
use middle::graph;
use middle::lang_items::QuietEarlyDropTraitLangItem;
use middle::cfg;
use middle::subst::Subst;
use middle::subst;
use middle::ty;
use middle::ty::TypeContents;
use middle::typeck::check;
use middle::typeck::infer;
use middle::typeck;
use middle::typeck::check::vtable::relate_trait_refs; // FIXME
use middle::typeck::check::vtable::connect_trait_tps; // FIXME
use middle::typeck::check::vtable::fixup_substs; // FIXME
use middle::typeck::check::vtable::fixup_ty; // FIXME
use middle::typeck::check::vtable::lookup_vtable_from_bounds; // FIXME
use middle::typeck::check::vtable::lookup_vtable; // FIXME
// use middle::typeck::check::vtable; // FIXME for some reason this is failing.  :(
use middle::typeck::check;
use util::ppaux::Repr;
use util::nodemap::DefIdMap;

use std::cell::RefCell;
use std::rc::Rc;
use std::collections::hashmap::HashMap;
use std::sync::atomics;
use syntax::{ast,ast_map,ast_util,codemap};
use syntax::attr::AttrMetaMethods;

static mut warning_count: atomics::AtomicUint = atomics::INIT_ATOMIC_UINT;

pub fn check_drops(bccx: &BorrowckCtxt,
                   flowed_move_data: &move_data::FlowedMoveData,
                   id: ast::NodeId,
                   cfg: &cfg::CFG,
                   decl: &ast::FnDecl,
                   body: &ast::Block) {
    debug!("check_drops(body id={:?})", body.id);

    let param_env;

    let mut cursor_id = id;
    loop {
        match bccx.tcx.map.find(cursor_id) {
            Some(ast_map::NodeItem(..)) => {
                let fn_pty = ty::lookup_item_type(bccx.tcx, ast_util::local_def(cursor_id));
                let generics = &fn_pty.generics;
                param_env = ty::construct_parameter_environment(bccx.tcx, generics, body.id);
                break;
            }

            // FIXME (pnkfelix): There used to be cut-and-pasted code
            // here that did the same thing as NodeItem case above,
            // but for NodeMethod and NodeTraitMethod. Those variants
            // do not exist anymore, but presumably they are still
            // separate cases under a different name.

            Some(_) => {
                cursor_id = bccx.tcx.map.get_parent(cursor_id);
                continue;
            }
            None => {
                fail!("could not find param_env for node {}", id);
            }
        }
    };

    cfg.graph.each_node(|node_index, node| {
        // Special case: do not flag violations for control flow from
        // return expressions.  Each return can be prefixed with
        // separate destructor invocation code specialized to whatever
        // paths need dropping.
        if node_index == cfg.exit {
            return true;
        }

        // Do not bother doing the query for unreachable portions of
        // the control flow graph.
        if !cfg.is_reachable(node_index) {
            return true;
        }

        // First, figure out if there is >1 incoming edge.
        {
            let mut how_many = 0u;
            cfg.graph.each_incoming_edge(node_index, |_edge_index, _edge| {
                how_many += 1;
                how_many <= 1 // keep looking until we see >1.
            });

            if how_many <= 1 {
                return true;
            }
        }

        // Okay, >1 incoming edge.
        //
        // Now we need to verify that all predecessor nodes establish
        // the same set of destruction obligations for the current
        // scope.
        //
        // We could just do a pairwise comparison, e.g. assume that the
        // first incoming edge is correct, then compare (1st, 2nd);
        // (2nd, 3rd); etc, until we encounter a difference, and then
        // report that as an error.
        //
        // However, under the (not yet validated) assumption that most
        // errors that we see will be missing calls to drop, we adopt
        // a different strategy: First, compute the intersection `I`
        // of the destruction obligations for all incoming edges.
        // Then compare each edge's destruction obligations against
        // `I`, and report all extra entries as needing to be
        // explicitly dropped on this edge (or to be reconstructed on
        // the edges where it was moved away).

        let move_data = &flowed_move_data.move_data;
        let needs_drop = &flowed_move_data.dfcx_needs_drop;
        let ignore_drop = &flowed_move_data.dfcx_ignore_drop;
        let path_count = move_data.paths.borrow().len();

        let intersection = needs_drop.bitset_for(dataflow::Entry, node_index);

        // In theory, that should be all we need to do; i.e. at this
        // point we should be able to compare each incoming node's
        // exit state with the computed intersection, and report any
        // deviation we see.
        //
        // HOWEVER: match arms complicate things.  In principle the
        // bindings introduced by the bindings on a match arm are
        // scoped to the match arm, and so for code like this:
        //
        //    match s {
        //        Ok(x)  => { Some(x) },
        //        Err(s) => { None },
        //    }
        //
        // you might expect that the `s` on the `Err(s)` branch is
        // dropped at the end of that arm.
        //
        // That's not how things are represented in the compiler,
        // unfortunately for us here; instead, the compiler see's the
        // lifetime of `s` as being the entire match expression, with
        // the drop of `s` tied to the flowgraph node for the match
        // itself, not each arm.
        //
        // pnkfelix tried to hack in support for representing the
        // narrower scope of each arm that fits his mental model, but
        // encountered some problems.
        //
        // So instead, we take this approach: instead of comparing
        // each incoming edge to the intersection above directly, now
        // compare each incoming edge to the intersection *after*
        // applying the kill bits for this merge point to both sides.
        // pnkfelix calls this "equivalence modulo merge-kills"
        //
        // This should take care of match patterns that will be
        // automatically destroyed, while leaving paths with a broader
        // scope than the match preserved.
        //
        // UPDATE: There is actually a more general principle we can
        // apply here, without worrying about match-arms: simply
        // walking forward looking if the end-of-scope for the
        // variable comes before any other side-effect.  If so, then
        // we can safely auto-drop without warning the user, since the
        // net effect is the same as if we still had a drop-flag.

        let mut intersection = intersection;
        needs_drop.apply_gen_kill(node_index, intersection.as_mut_slice());
        let intersection = intersection;

        cfg.graph.each_incoming_edge(node_index, |edge_index, edge| {
            let source = edge.source();
            let mut temp = needs_drop.bitset_for(dataflow::Exit, source);

            // see note above about "equivalence modulo merge-kills"
            //
            // But also, this hack can probably go away with new
            // "scan-ahead-for-scope-end" rule
            needs_drop.apply_gen_kill(node_index, temp.as_mut_slice());

            if temp != intersection {
                let source_id = cfg.graph.node(source).data.id;
                let opt_source_span = bccx.tcx.map.opt_span(source_id);
                needs_drop.each_bit_for_node(dataflow::Exit, source, |bit_idx| {
                    if !cfg.is_reachable(source) ||
                        dataflow::is_bit_set(intersection.as_slice(), bit_idx) {
                        return true;
                    }

                    let paths = move_data.paths.borrow();
                    let path = paths.get(bit_idx);
                    let lp = &path.loan_path;

                    let ignored_paths = ignore_drop.bitset_for(dataflow::Exit, source);
                    if dataflow::is_bit_set(ignored_paths.as_slice(), bit_idx) {
                        debug!("check_drops can ignore lp={} as it is non-drop on this path.",
                               lp.repr(bccx.tcx));
                        return true;
                    }

                    // Check if there is a single effect-free
                    // successor chain that leads to the end of the
                    // scope of the local variable at the base of `lp`
                    // (and therefore we can safely auto-drop `lp`
                    // without warning the user)
                    let kill_id = lp.kill_id(bccx.tcx);
                    match scan_forward_for_kill_id(bccx, cfg, node_index, kill_id)
                    {
                        FoundScopeEndPure => {
                            debug!("check_drops can ignore lp={} as its scope-end is imminent.",
                                   lp.repr(bccx.tcx));
                            return true;
                        }
                        AbandonedScan => {}
                    }

                    // At this point, we are committed to reporting a warning to the user
                    let count = unsafe {
                        warning_count.fetch_add(1, atomics::Relaxed) + 1
                    };

                    let loan_path_str = bccx.loan_path_to_string(lp.deref());

                    let cfgidx_and_id = format!(" (cfgidx={}, id={})", source, source_id);
                    let where_ = if bccx.tcx.sess.verbose() {
                        cfgidx_and_id.as_slice()
                    } else {
                        ""
                    };

                    let msg = format!("Storage at `{:s}` is left initialized on some paths \
                                       exiting here{:s}, but uninitialized on others. \
                                       (Consider either using Option, or calling `drop()` \
                                       on it or reinitializing it as necessary); count: {}",
                                      loan_path_str, where_, count);

                    // Check if type of `lp` has #[quiet_early_drop]
                    // attribute or implements `QuietEarlyDrop`;
                    // select the appropriate lint to signal.
                    let lint_category = if is_quiet_early_drop_lp(bccx.tcx, &param_env, &**lp) {
                        lint::builtin::QUIET_EARLY_DROP
                    } else {
                        lint::builtin::UNMARKED_EARLY_DROP
                    };
                    bccx.tcx.sess.add_lint(lint_category,
                                           source_id,
                                           opt_source_span.unwrap_or(codemap::DUMMY_SP),
                                           msg);

                    if false { cfg.graph.each_incoming_edge(node_index, |edge_index, edge| {
                        let source2 = edge.source();
                        if !cfg.is_reachable(source2) {
                            return true;
                        }

                        let temp2 = needs_drop.bitset_for(dataflow::Exit, source2);
                        let mut count = 0u;
                        if !dataflow::is_bit_set(temp2.as_slice(), bit_idx) {
                            count += 1;
                            let source2_id = cfg.graph.node(source2).data.id;
                            let opt_source2_span = bccx.tcx.map.opt_span(source2_id);
                            let cfgidx_and_id = format!(" (cfgidx={}, id={})",
                                                        source2, source2_id);
                            let where_ = if bccx.tcx.sess.verbose() {
                                cfgidx_and_id.as_slice()
                            } else {
                                ""
                            };
                            let msg = format!("Path {:u} here{:s} leaves `{:s}` \
                                               uninitialized.",
                                              count, where_, loan_path_str);
                            match opt_source2_span {
                                Some(span) => bccx.tcx.sess.span_note(span, msg.as_slice()),
                                None => bccx.tcx.sess.note(msg.as_slice()),
                            }
                        }
                        true
                    }); }

                    true
                });
            }

            true
        });

        true
    });
}

// This uses an enum rather than a bool to support future handling of
// walking over paths with potentially significant effects; e.g. see
// notes below with ExprPath.
#[deriving(PartialEq)]
enum ForwardScanResult {
    FoundScopeEndPure,
    AbandonedScan,
}

fn scan_forward_for_kill_id(bccx: &BorrowckCtxt,
                            cfg: &cfg::CFG,
                            start: cfg::CFGIndex,
                            kill_id: ast::NodeId) -> ForwardScanResult {
    //! returns true only if there is a unique effect-free successor
    //! chain from `start` to `kill_id` or to `cfg.exit`

    let mut cursor = start;
    loop {
        debug!("fwd-scan for kill_id={} cursor={}", kill_id, cursor);
        let mut count = 0u;
        let mut successor = None;
        cfg.graph.each_outgoing_edge(cursor, |edge_index, edge| {
            debug!("fwd-scan cursor={} edge.target={}", cursor, edge.target());
            successor = Some(edge_index);
            count += 1;
            count <= 1
        });

        if count != 1 {
            debug!("fwd-scan: broken successor chain; give up");
            return AbandonedScan;
        }

        cursor = cfg.graph.edge(successor.unwrap()).target();
        if cursor == cfg.exit {
            debug!("fwd-scan: success (hit exit), no need for warning");
            return FoundScopeEndPure;
        }

        let successor_id = cfg.graph.node(cursor).data.id;
        if successor_id == ast::DUMMY_NODE_ID {
            debug!("fwd-scan: dummy node in flow graph; give up");
            return AbandonedScan;
        }

        if successor_id == kill_id {
            debug!("fwd-scan: success (hit {}), no need for warning", kill_id);
            return FoundScopeEndPure;
        }

        match bccx.tcx.map.get(successor_id) {
            // See notes below about ExprPath handling.  Note that
            // NodeLocal and NodeArg correespond to binding sites, not
            // uses. Skipping these is likely to not matter too much
            // until some ExprPath's are treated as pure.
            ast_map::NodeLocal(_) |
            ast_map::NodeArg(_)   |
            ast_map::NodeBlock(_) => {
                debug!("fwd-scan: node {} effect-free; continue looking",
                       successor_id);
                continue;
            }

            ast_map::NodeExpr(e) => {
                // Keep in mind when reading these cases that the
                // NodeId associated with an expression node like
                // ExprIf is at the *end* of the expression, where the
                // two arms of the if meet.
                match e.node {
                    // node is where arms of match meet.
                    ast::ExprMatch(..) |
                    // node is where block exits.
                    ast::ExprBlock(..) |
                    // (<expr>) is definitely pure.
                    ast::ExprParen(..) |
                    // node is after arg is evaluated; before return itself.
                    ast::ExprRet(..)   |
                    // node is where arms of if meet.
                    ast::ExprIf(..) => {
                        debug!("fwd-scan: expr {} effect-free; \
                                continue looking",
                               successor_id);
                        continue;
                    }

                    // variable lookup
                    ast::ExprPath(ref p) => {
                        // Strictly speaking, this is an observable
                        // effect. In particular, if a destructor has
                        // access to the address of this path and
                        // imperatively overwrites it, then a client
                        // will care about the drop order.
                        //
                        // A captured `&mut`-ref cannot actually alias
                        // such a path, according to Rust's borrowing
                        // rules. Therefore, the scenario only arises
                        // with either (1.) a `*mut`-pointer or (2.) a
                        // `&`-ref to a type with interior mutability
                        // (type_interior_is_unsafe). Still, it can
                        // arise.
                        //
                        // The easy conservative approach is to simply
                        // treat this as an effect and abandon the
                        // forward-scan.

                        // FIXME: A less-conservative but still sound
                        // approach would be to treat reads of
                        // non-local variables that had never been
                        // borrowed as effect-free as well, and it
                        // would probably cover many cases of
                        // interest.  We can put that in later
                        // (pnkfelix).

                        // FIXME: A "less sound" but potentially
                        // useful approach would be to further tier
                        // the lint structure here to allow the user
                        // to specify whether all variable-reads
                        // should be treated as pure.  But I am
                        // hesistant to make that part of the default
                        // set of lints, at least for now (pnkfelix).

                        debug!("fwd-scan: expr {} path read {} \
                                potentially effectful; give up",
                               successor_id, p);

                        return AbandonedScan;
                    }

                    _ => {
                        debug!("fwd-scan: expr {} potentially effectful; \
                                give up",
                               successor_id);
                        return AbandonedScan;
                    }

                }
            }

            ast_map::NodeStmt(_)       |
            ast_map::NodePat(_) |
            ast_map::NodeStructCtor(_) => {
                debug!("fwd-scan: node {} potentially effectful; give up",
                       successor_id);
                return AbandonedScan;
            }

            ast_map::NodeItem(_)        | ast_map::NodeForeignItem(_) |
            ast_map::NodeVariant(_)     | ast_map::NodeLifetime(_) => {
                bccx.tcx.sess.bug("unexpected node")
            }
        }
    }
}

fn is_quiet_early_drop_lp(tcx: &ty::ctxt,
                          param_env: &ty::ParameterEnvironment,
                          lp: &LoanPath) -> bool {
    let t = lp.to_type(tcx);
    let ret = is_quiet_early_drop_ty(tcx, param_env, t);
    debug!("is_quiet_early_drop_lp: {} is {}", lp.repr(tcx), ret);
    ret
}


fn is_quiet_early_drop_ty(tcx: &ty::ctxt,
                          param_env: &ty::ParameterEnvironment,
                          t: ty::t) -> bool {
    match ty::get(t).sty {
        ty::ty_struct(did, _) |
        ty::ty_enum(did, _) => {
            let found_attr = with_attrs_for_did(tcx, did, |attrs| {
                for attr in attrs.iter() {
                    if attr.check_name("quiet_early_drop") {
                        return true
                    }
                }
                return false;
            });
            if found_attr {
                return true;
            }
        }
        _ => {}
    }

    // Okay, so far we know that the type does not have the
    // `quiet_early_drop` attribute marker.

    let opt_trait_did = tcx.lang_items.require(QuietEarlyDropTraitLangItem);
    let trait_did = match opt_trait_did {
        Ok(trait_did) => trait_did,
        Err(_) => {
            // if there is no `QuietEarlyDrop` lang item, then
            // just do not bother trying to handle this case.
            return false;
        }
    };
    is_quiet_early_drop_ty_recur(tcx, param_env, trait_did, t)
}

fn is_quiet_early_drop_ty_recur(tcx: &ty::ctxt,
                                param_env: &ty::ParameterEnvironment,
                                trait_did: ast::DefId,
                                t: ty::t) -> bool {

    // The main base case: if the type implements `QuietEarlyDrop`,
    // then we stop looking.
    let implements = type_implements_trait(tcx, param_env, t, trait_did);
    debug!("is_quiet_early_drop_ty_recur: type_implements_trait({}) is {}",
           t.repr(tcx), implements);
    if implements {
        return true;
    }

    // If it does not implement the QuietEarlyDrop trait, then we need
    // to emulate the traversal done by `type_contents`, looking at
    // the substructure of the type to see if the type (or any part of
    // it) "drops loudly", i.e., implements Drop but does not
    // implement QuietEarlyDrop.

    let drops_quiet = || {
        let ret = true;
        debug!("is_quiet_early_drop_ty_recur: {} fallthru base case: {}", t.repr(tcx), ret);
        ret
    };

    let drops_loud = || {
        let ret = false;
        debug!("is_quiet_early_drop_ty_recur: {} fallthru base case: {}", t.repr(tcx), ret);
        ret
    };

    let drops_recur = |f:|| -> bool| {
        debug!("is_quiet_early_drop_ty_recur: {} fallthru recur entry", t.repr(tcx));
        let ret = f();
        debug!("is_quiet_early_drop_ty_recur: {} fallthru recur ret: {}", t.repr(tcx), ret);
        ret
    };

    let recur = |ty| is_quiet_early_drop_ty_recur(tcx, param_env, trait_did, ty);

    match ty::get(t).sty {
        ty::ty_nil |
        ty::ty_bot |
        ty::ty_bool |
        ty::ty_char |
        ty::ty_int(_) |
        ty::ty_uint(_) |
        ty::ty_float(_) |
        ty::ty_str |
        ty::ty_bare_fn(_) |
        ty::ty_rptr(_, _) |
        ty::ty_err => drops_quiet(),

        ty::ty_box(_) |
        ty::ty_uniq(_) |
        ty::ty_ptr(_) |
        ty::ty_infer(_) |
        ty::ty_unboxed_closure(..) => drops_loud(),

        ty::ty_param(_) => drops_loud(),

        ty::ty_trait(_) => drops_loud(),

        ty::ty_closure(ref f) => {
            match f.store {
                // by-ref closure
                ty::RegionTraitStore(..) => drops_quiet(),
                ty::UniqTraitStore => drops_loud(),
            }
        }

        // (Below are all the potentially recursive cases)

        ty::ty_tup(ref tys) => drops_recur(|| tys.iter().all(|&ty| recur(ty))),
        ty::ty_vec(ty, opt_len) => drops_recur(|| recur(ty)),

        ty::ty_enum(def_id, ref substs) => {
            // if this type *itself* has a dtor, but does not
            // implment `QuietEarlyDrop`, then it must drop loudly.
            if ty::has_dtor(tcx, def_id) {
                drops_loud()
            } else {
                let variants = ty::substd_enum_variants(tcx, def_id, substs);
                drops_recur(|| variants.iter()
                            .flat_map(|v| v.args.iter())
                            .all(|&ty| recur(ty)))
            }
        }

        ty::ty_struct(def_id, ref substs) => {
            // if this type *itself* has a dtor, but does not
            // implment `QuietEarlyDrop`, then it must drop loudly.
            if ty::has_dtor(tcx, def_id) {
                drops_loud()
            } else {
                drops_recur(|| ty::struct_fields(tcx, def_id, substs).iter()
                            .map(|field| field.mt.ty)
                            .all(|ty| recur(ty)))
            }
        }

    }
}

fn with_attrs_for_did<A>(tcx: &ty::ctxt,
                         did: ast::DefId,
                         f: |&[ast::Attribute]| -> A) -> A {
    if ast_util::is_local(did) {
        match tcx.map.get(did.node) {
            ast_map::NodeItem(it) => f(it.attrs.as_slice()),
            _ => fail!("must have entry for struct or enum"),
        }
    } else {
        // FIXME: interface of `get_item_attrs` could be generalized
        // to support this directly.
        let mut result = None;
        csearch::get_item_attrs(&tcx.sess.cstore, did, |attrs| {
            result = Some(f(attrs.as_slice()))
        });
        result.unwrap()
    }
}

fn type_implements_trait(tcx: &ty::ctxt,
                         param_env: &ty::ParameterEnvironment,
                         ty: ty::t,
                         trait_did: ast::DefId) -> bool {
    // largely modelled after lookup_vtable

    let infcx = infer::new_infer_ctxt(tcx);
    let span = codemap::DUMMY_SP;
    let substs = subst::Substs::empty();

    let trait_def = ty::lookup_trait_def(tcx, trait_did);
    let trait_ref = &trait_def.trait_ref;

    debug!("type_implements_trait ty={} trait_ref={}",
           ty.repr(tcx),
           trait_ref.repr(tcx));

    ty::populate_implementations_for_trait_if_necessary(tcx, trait_ref.def_id);

    let substs = substs.with_self_ty(ty);

    // Substitute the values of the type parameters that may
    // appear in the bound.
    debug!("about to subst: {}, {}", trait_ref.repr(tcx), substs.repr(tcx));
    let trait_ref = trait_ref.subst(tcx, &substs);

    debug!("after subst: {}", trait_ref.repr(tcx));

    let unboxed_closures = RefCell::new(DefIdMap::new());

    let vcx = check::vtable::VtableContext {
        infcx: &infcx,
        param_bounds: &param_env.bounds,
        unboxed_closures: &unboxed_closures,
        is_early: check::vtable::NotEarly,
        if_missing_ty_param: check::vtable::IfMissingTyParamGiveUp,
    };

    match lookup_vtable(&vcx, span, ty, trait_ref) {
        Ok(Some(_)) => true,
        Ok(None) | Err(_) => false,
    }
}
