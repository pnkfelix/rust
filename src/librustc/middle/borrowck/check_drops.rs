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

        let intersection = {
            // (it doesn't matter which index we grab this from, we going
            // to fill it with ones anyway.)
            let mut temp = needs_drop.bitset_for(dataflow::Entry, node_index);
            for u in temp.mut_iter() { *u = -1 as uint; }
            cfg.graph.each_incoming_edge(node_index, |_edge_index, edge| {
                let source = edge.source();
                needs_drop.apply_op(dataflow::Exit,
                                    source,
                                    temp.as_mut_slice(),
                                    dataflow::Intersect);
                true
            });
            temp
        };

        cfg.graph.each_incoming_edge(node_index, |edge_index, edge| {
            let source = edge.source();
            let temp = needs_drop.bitset_for(dataflow::Exit, source);
            if temp != intersection {
                let source_span = ty::expr_span(bccx.tcx, cfg.graph.node(source).data.id);
                needs_drop.each_bit_for_node(dataflow::Exit, source, |bit_idx| {
                    if dataflow::is_bit_set(intersection.as_slice(), bit_idx) {
                        return true;
                    }

                    let paths = move_data.paths.borrow();
                    let path = paths.get(bit_idx);
                    let lp = &path.loan_path;
                    let loan_path_str = bccx.loan_path_to_string(lp.deref());

                    bccx.tcx.sess.span_warn(
                        source_span,
                        format!("Storage at {:s} is left initialized here, but \
                                 uninitialized on other control flow paths.",
                                loan_path_str).as_slice());

                    cfg.graph.each_incoming_edge(node_index, |edge_index, edge| {
                        let source2 = edge.source();
                        let temp2 = needs_drop.bitset_for(dataflow::Exit, source2);
                        let mut count = 0u;
                        if dataflow::is_bit_set(temp2.as_slice(), bit_idx) {
                            count += 1;
                            let source2_span = ty::expr_span(bccx.tcx,
                                                             cfg.graph.node(source2).data.id);
                            bccx.tcx.sess.span_note(
                                source2_span,
                                format!("This is path {} that leaves {:s} uninitialized.",
                                        count, loan_path_str).as_slice())
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
