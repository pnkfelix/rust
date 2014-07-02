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
use middle::graph;
use middle::cfg;
use middle::ty;
use middle::ty::TypeContents;
use std::rc::Rc;
use std::collections::hashmap::HashMap;
use syntax::{ast,ast_map};

pub fn check_dtors(bccx: &BorrowckCtxt,
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
        // scope: namely, the same set of assigned paths (establishing
        // future destruction obligations) and moved paths (removing a
        // previously established destruction obligation).


        // DEBUGGING/INSTRUMENTATION CODE FOLLOWS.

        // First pass: find out which assigns/moves differ between
        // incoming edges (the ones that do not differ we do not need
        // to warn about.)  These tables map each assignment (move) to
        // a tuple `(count,last)`, where: `count` is how many edges
        // from which this loan path was seen assigned (moved) , and
        // `last` is the most recent edge that we saw this loan path
        // assigned (moved) on.

        type EdgeCountMap = HashMap<Rc<LoanPath>, (graph::EdgeIndex, uint)>;
        let mut merged_assigns : EdgeCountMap = HashMap::new();
        let mut merged_moves : EdgeCountMap = HashMap::new();

        let mut incoming_edge_count = 0u;
        cfg.graph.each_incoming_edge(node_index, |edge_index, edge| {
            incoming_edge_count += 1;

            let source = edge.source();
            let move_data = &flowed_move_data.move_data;

            flowed_move_data.dfcx_assign.each_bit_on_exit_frozen(source, |index| {
                let assignments = move_data.var_assignments.borrow();
                let assignment = assignments.get(index);
                let where = assignment.id;
                let lp = move_data.path_loan_path(assignment.path);
                debug!("  unfiltered source: {} assigns loan_path: {:s} at {}",
                       source, bccx.loan_path_to_string(lp.deref()), where);
                merged_assigns.insert_or_update_with(
                    lp.clone(),
                    (edge_index, 1),
                    |k, &(ref mut old_edge_index, ref mut count)| {
                        // If its a new edge, increment; otherwise leave alone.
                        if *old_edge_index != edge_index {
                            *old_edge_index = edge_index;
                            *count = *count + 1
                        }
                    });
                true
            });

            flowed_move_data.dfcx_moves.each_bit_on_exit_frozen(source, |index| {
                let moves = move_data.moves.borrow();
                let move = moves.get(index);
                let where = move.id;
                let lp = move_data.path_loan_path(move.path);
                debug!("  unfiltered source: {} moves loan_path: {:s} at {}",
                       source, bccx.loan_path_to_string(lp.deref()), where);
                merged_moves.insert_or_update_with(
                    lp.clone(),
                    (edge_index, 1),
                    |k,&(ref mut old_edge_index, ref mut count)| {
                        // If its a new edge, increment; otherwise leave alone.
                        if *old_edge_index != edge_index {
                            *old_edge_index = edge_index;
                            *count = *count + 1;
                        }
                    });
                true
            });
            true
        });

        cfg.graph.each_incoming_edge(node_index, |edge_index, edge| {
            let source = edge.source();
            let source_id = cfg.graph.node_data(edge.source()).id;
            debug!("check_dtors node_index: {} node.data.id: {} \
                                edge_index: {} edge.data: {} \
                                source: {} source_id: {} \
                   ",
                   node_index, node.data.id,
                   edge_index, edge.data,
                   source, source_id);

            let move_data::FlowedMoveData {
                ref move_data,
                dfcx_moves: ref move_bits,
                dfcx_assign: ref assign_bits } = *flowed_move_data;

            assign_bits.each_bit_on_exit_frozen(source, |index| {
                let assignments = move_data.var_assignments.borrow();
                let assignment = assignments.get(index);
                let where = assignment.id;
                let lp = move_data.path_loan_path(assignment.path);
                if merged_assigns.find(&lp).unwrap().val1() < incoming_edge_count {
                    debug!("  source: {} assigns loan_path: {:s} at {}",
                           source, bccx.loan_path_to_string(lp.deref()), where);
                }
                true
            });

            move_bits.each_bit_on_exit_frozen(source, |index| {
                let moves = move_data.moves.borrow();
                let move = moves.get(index);
                let lp = move_data.path_loan_path(move.path);
                let move_count = merged_moves.find(&lp).unwrap().val1();
                let assign_count = match merged_assigns.find(&lp) {
                    Some(v) => v.val1(),
                    None => 0
                };

                assert!(move_count <= incoming_edge_count);

                let loan_path_str = bccx.loan_path_to_string(lp.deref());
                debug!("  source: {} moves loan_path: {:s} at {}, \
                          incoming: {} moves: {} assigns: {}",
                       source, loan_path_str, move.id,
                       incoming_edge_count, move_count, assign_count);

                if move_count == incoming_edge_count {
                    return true;
                }

                // arguably this should be the condition being checked
                // here, not the one above.  The heart of what I am
                // encountering (I think) is that when you have merge
                // points A -> B; A -> C; B -> D; C -> D; where some
                // path is only in scope for B (and in particular, not
                // A) then the above is currently flagging the path as
                // breaking the rule on the edge B -> D, because it
                // sees no corresponding move on the edge C -> D.  But
                // that seems crazy, since the path in question is not
                // even in scope at that point.
                //
                // On the other hand, I don't know if the treatment of
                // substructural paths means that my original model
                // was better.  We will see.  For now, allow us to
                // bail out when we have #moves == #assigns, but do it
                // loudly.
                if assign_count == move_count {
                    let move_span = bccx.tcx.map.span(move.id);
                    bccx.tcx.sess.span_note(
                        move_span,
                        format!("{:s} might be acceptable since \
                                 moves {} == assigns {}",
                                loan_path_str,
                                move_count, assign_count).as_slice());
                }

                // At this point, some but not all paths move `lp`.
                // But that is okay if `lp` has type of kind `Copy`.
                let expr_ty = match bccx.tcx.map.find(move.id) {
                    Some(ast_map::NodeExpr(e)) =>
                        ty::expr_ty_adjusted(bccx.tcx, &*e),

                    // XXX is there an analogue of expr_ty_adjusted
                    // for pat? or does auto-ref/auto-deref never
                    // arise in that context? guessing it does not.
                    Some(ast_map::NodeLocal(p)) => ty::pat_ty(bccx.tcx, &*p),

                    r => bccx.tcx.sess.bug(format!("MoveExpr({:?}) maps to \
                                                   {:?}, not Expr nor Local",
                                                   move.id,
                                                   r).as_slice()),
                };
                if ty::type_is_copy(bccx.tcx, expr_ty) {
                    return true;
                }

                // Some but not all paths move `lp`, and `lp` is an
                // expression of non-copy type; therefore we have
                // found "all-paths-drop-equally" violation.

                let loan_path_str = bccx.loan_path_to_string(lp.deref());
                debug!("  source: {} moves loan_path: {:s} at {}",
                       source, loan_path_str, move.id);

                let move_span = bccx.tcx.map.span(move.id);
                bccx.tcx.sess.span_warn(
                    move_span,
                    format!("Storage at {:s} is left initialized on \
                             {} paths and uninitialized on {} others.",
                            loan_path_str,
                            assign_count, move_count).as_slice());

                // XXX Idea: if the assignment count == (>=?)
                // incoming_edge_count then that is a hint that there
                // is a drop/move on some paths and not on the others,
                // so in that case, focus on that.

                // XXX Another idea: Maybe just use whether assignment
                // count > move count to decide which aspect to focus
                // on in the output.

                assign_bits.each_bit_on_exit_frozen(source, |index| {
                    let assignments = move_data.var_assignments.borrow();
                    let assignment = assignments.get(index);
                    let assigned_lp = move_data.path_loan_path(assignment.path);
                    if assigned_lp == lp {
                        bccx.tcx.sess.span_note(
                            assignment.span,
                            format!("{:s} assigned here", loan_path_str).as_slice());
                    }
                    true
                });


                // We loop over the dfcx_moves here, to provide a
                // uniform presentation of the assignments and moves
                // together.  But since we are already in the midst of
                // looping over them in outer loop, we will encounter
                // each violating move in turn, so this loop is really
                // totally redundant, at least in principle.

                move_bits.each_bit_on_exit_frozen(source, |index| {
                    let submove = moves.get(index);
                    let submove_lp = move_data.path_loan_path(submove.path);
                    let submove_span = bccx.tcx.map.span(submove.id);
                    if submove_lp == lp {
                        bccx.tcx.sess.span_note(
                            submove_span,
                            format!("{:s} moved here", loan_path_str).as_slice());
                    }
                    true
                });

                true
            });
            true
        });

        true
    });
}
