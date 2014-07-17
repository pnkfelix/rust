// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// Data structures for tracking which paths are scheduled for
/// eventual dropping (as opposed to paths that has been moved, and
/// thus the drop obligation has been shifted to the receiver of the
/// move).
///
/// The goal is to identify control-flow join points where one
/// predecessor node has a path that needs to be eventually dropped
/// while that same path has been moved away on another predecessor
/// node. Such join points will probably become illegal in the future
/// (so that the set of dropped state is equivalent on all
/// control-flow paths, and thus the drop-flag can be removed from
/// droppable structures).

use std::collections::{HashMap, HashSet};
use middle::borrowck::*;
use middle::cfg;
use middle::dataflow::DataFlowContext;
use middle::dataflow::BitwiseOperator;
use middle::dataflow;
use euv = middle::expr_use_visitor;
use mc = middle::mem_categorization;
use syntax::ast;
use syntax::ast_util;

struct NeedsDropCtxt<'a> {
    paths: uint,
}

impl<'a> euv::Delegate for NeedsDropCtxt<'a> {
    // The value found at `cmt` is either copied or moved, depending
    // on mode.
    fn consume(&mut self,
               consume_id: ast::NodeId,
               consume_span: Span,
               cmt: mc::cmt,
               mode: ConsumeMode) {
        unimplemented!()
    }

    // The value found at `cmt` is either copied or moved via the
    // pattern binding `consume_pat`, depending on mode.
    fn consume_pat(&mut self,
                   consume_pat: &ast::Pat,
                   cmt: mc::cmt,
                   mode: ConsumeMode) {
        unimplemented!()
    }

    // The value found at `borrow` is being borrowed at the point
    // `borrow_id` for the region `loan_region` with kind `bk`.
    fn borrow(&mut self,
              borrow_id: ast::NodeId,
              borrow_span: Span,
              cmt: mc::cmt,
              loan_region: ty::Region,
              bk: ty::BorrowKind,
              loan_cause: LoanCause) {
        unimplemented!()
    }

    // The local variable `id` is declared but not initialized.
    fn decl_without_init(&mut self,
                         id: ast::NodeId,
                         span: Span) {
        unimplemented!()
    }

    // The path at `cmt` is being assigned to.
    fn mutate(&mut self,
              assignment_id: ast::NodeId,
              assignment_span: Span,
              assignee_cmt: mc::cmt,
              mode: MutateMode) {
        unimplemented!()
    }
}

#[deriving(Clone)]
pub struct Operator;

pub type NeedsDropDataFlow<'a> = DataFlowContext<'a, Operator>;



pub struct NeedsDropData<'a> {
    pub dfcx: NeedsDropDataFlow<'a>,
}

impl<'a> NeedsDropData<'a> {
    pub fn new(bccx: &mut BorrowckCtxt<'a>,
               id_range: ast_util::IdRange,
               decl: &ast::FnDecl,
               cfg: &cfg::CFG,
               body: &ast::Block) -> NeedsDropData<'a> {
        debug!("needs_drop::check_control_paths(body id={:?})", body.id);

        let mut ndcx = NeedsDropCtxt {
            paths: 0,
        };

        {
            let mut euv = euv::ExprUseVisitor::new(&mut ndcx, bccx.tcx);
            euv.walk_fn(decl, body);
        }

        let len = ndcx.paths;

        let mut dfcx =
            DataFlowContext::new(bccx.tcx,
                                 "needs_drop",
                                 Some(decl),
                                 cfg,
                                 Operator,
                                 id_range,
                                 len);

        NeedsDropData {
            dfcx: dfcx,
        }
    }
}

impl dataflow::BitwiseOperator for Operator {
    /// Joins two predecessor bits together, typically either `|` or `&`
    fn join(&self, succ: uint, pred: uint) -> uint {
        succ | pred
    }
}

impl dataflow::DataFlowOperator for Operator {
    /// Specifies the initial value for each bit in the `on_entry` set
    fn initial_value(&self) -> bool {
        // nothing needs to be dropped until it is initialized.
        // E.g. `let x;` should be initialized as not needing to be
        // dropped.  (Other things like function parameters are of
        // course implicitly initialized and are handled accordingly.)
        false
    }
}
