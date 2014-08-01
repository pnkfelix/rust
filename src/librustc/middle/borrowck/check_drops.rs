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

use middle::borrowck::*;
use middle::borrowck::move_data::{Assignment, Move};
use euv = middle::expr_use_visitor;
use mc = middle::mem_categorization;
use middle::dataflow;
use middle::graph;
use middle::cfg;
use middle::ty;
use middle::ty::TypeContents;
use std::rc::Rc;
use std::collections::hashmap::HashMap;
use syntax::{ast,ast_map};

pub fn check_drops(bccx: &BorrowckCtxt,
                   flowed_move_data: &move_data::FlowedMoveData,
                   cfg: &cfg::CFG,
                   decl: &ast::FnDecl,
                   body: &ast::Block) {
    debug!("check_dtors(body id={:?})", body.id);

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
                    let loan_path_str = bccx.loan_path_to_string(lp.deref());

                    let cfgidx_and_id = format!(" (cfgidx={}, id={})", source, source_id);
                    let where = if bccx.tcx.sess.verbose() {
                        cfgidx_and_id.as_slice()
                    } else {
                        ""
                    };

                    let msg = format!("Storage at `{:s}` is left initialized here{:s}, \
                                       but uninitialized on other control flow paths. \
                                       (Consider either calling `drop()` on it here, \
                                       or reinitializing it on the other paths)",
                                      loan_path_str, where);

                    match opt_source_span {
                        Some(span) => bccx.tcx.sess.span_warn(span, msg.as_slice()),
                        None => bccx.tcx.sess.warn(msg.as_slice()),
                    }
                    cfg.graph.each_incoming_edge(node_index, |edge_index, edge| {
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
                            let where = if bccx.tcx.sess.verbose() {
                                cfgidx_and_id.as_slice()
                            } else {
                                ""
                            };
                            let msg = format!("Path {:u} here{:s} leaves `{:s}` \
                                               uninitialized.",
                                              count, where, loan_path_str);
                            match opt_source2_span {
                                Some(span) => bccx.tcx.sess.span_note(span, msg.as_slice()),
                                None => bccx.tcx.sess.note(msg.as_slice()),
                            }
                        }
                        true
                    });

                    true
                });
            }

            true
        });

        true
    });
}
