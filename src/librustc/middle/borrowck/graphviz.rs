/// This module provides linkage between rustc::middle::graph and
/// libgraphviz traits, specialized to attaching borrowck analysis
/// data to rendered labels.

/// For clarity, rename the graphviz crate locally to dot.
use dot = graphviz;
pub use middle::cfg::graphviz::{Node, Edge};
use cfg_dot = middle::cfg::graphviz;

use driver;
use driver::{GraphAnalysisVariant,Loans,Moves,Assigns};
use middle::borrowck;
use middle::borrowck::{BorrowckCtxt, LoanPath};

use syntax::ast;

use std::rc::Rc;
use std::str;


pub struct DataflowLabeller<'a> {
    pub inner: cfg_dot::LabelledCFG<'a>,
    pub variant: driver::GraphAnalysisName,
    pub borrowck_ctxt: &'a BorrowckCtxt<'a>,
    pub analysis_data: &'a borrowck::AnalysisData<'a>,
}

impl<'a> DataflowLabeller<'a> {
    fn dataflow_prefix_for(&self, n: &Node<'a>) -> String {
        let id = n.val1().data.id;
        debug!("dataflow_prefix_for(id={}) {}", id, self.variant.short_name());
        match self.variant {
            driver::DataflowAllVariants => self.dataflow_all_on_entry_for(n),
            driver::Dataflow(v) => self.dataflow_prefix_for_variant(n, v),
        }
    }

    fn dataflow_suffix_for(&self, n: &Node<'a>) -> String {
        let cfgidx = n.val0();
        debug!("dataflow_suffix_for(cfgidx={}) {}", cfgidx, self.variant.short_name());
        match self.variant {
            driver::DataflowAllVariants => self.dataflow_all_on_exit_for(n),
            driver::Dataflow(v) => self.dataflow_suffix_for_variant(n, v),
        }
    }

    fn dataflow_all_on_entry_for(&self, n: &Node<'a>) -> String {
        let mut sets = "".to_string();
        let mut seen_one = false;
        for &v in [Loans, Moves, Assigns].iter() {
            if seen_one { sets.push_str(" "); } else { seen_one = true; }
            sets.push_str(v.short_name());
            sets.push_str(": ");
            sets.push_str(self.dataflow_prefix_for_variant(n, v).as_slice());
        }
        sets
    }

    fn dataflow_all_on_exit_for(&self, n: &Node<'a>) -> String {
        let mut sets = "".to_string();
        let mut seen_one = false;
        for &v in [Loans, Moves, Assigns].iter() {
            if seen_one { sets.push_str(" "); } else { seen_one = true; }
            sets.push_str(v.short_name());
            sets.push_str(": ");
            sets.push_str(self.dataflow_suffix_for_variant(n, v).as_slice());
        }
        sets
    }

    fn dataflow_prefix_for_variant(&self, n: &Node, v: GraphAnalysisVariant) -> String {
        match v {
            Loans => self.dataflow_loans_on_entry_for(n),
            Moves => self.dataflow_moves_on_entry_for(n),
            Assigns => self.dataflow_assigns_on_entry_for(n),
        }
    }

    fn dataflow_suffix_for_variant(&self, n: &Node, v: GraphAnalysisVariant) -> String {
        match v {
            Loans => self.dataflow_loans_on_exit_for(n),
            Moves => self.dataflow_moves_on_exit_for(n),
            Assigns => self.dataflow_assigns_on_exit_for(n),
        }
    }

    fn dataflow_loans_on_entry_for(&self, n: &Node<'a>) -> String {
        let id = n.val1().data.id;
        let mut prefix = "{".to_string();
        let mut saw_prefix = false;
        let loans = &self.analysis_data.loans;
        if id != ast::DUMMY_NODE_ID {
            loans.each_bit_on_entry_frozen(id, |index| {
                let lp = self.loan_index_to_path(index);
                self.append_loan(&*lp, saw_prefix, &mut prefix);
                saw_prefix = true;
                true
            });
        }
        prefix.append("}")
    }

    fn dataflow_moves_on_entry_for(&self, n: &Node<'a>) -> String {
        let id = n.val1().data.id;
        let mut prefix = "{".to_string();
        let mut saw_prefix = false;
        let moves = &self.analysis_data.move_data.dfcx_moves;
        if id != ast::DUMMY_NODE_ID {
            moves.each_bit_on_entry_frozen(id, |index| {
                let lp = self.move_index_to_path(index);
                self.append_loan(&*lp, saw_prefix, &mut prefix);
                saw_prefix = true;
                true
            });
        }
        prefix.append("}")
    }

    fn dataflow_assigns_on_entry_for(&self, n: &Node<'a>) -> String {
        let id = n.val1().data.id;
        let mut prefix = "{".to_string();
        let mut saw_prefix = false;
        let assigns = &self.analysis_data.move_data.dfcx_assign;
        if id != ast::DUMMY_NODE_ID {
            assigns.each_bit_on_entry_frozen(id, |index| {
                let lp = self.assign_index_to_path(index);
                self.append_loan(&*lp, saw_prefix, &mut prefix);
                saw_prefix = true;
                true
            });
        }
        prefix.append("}")
    }

    fn dataflow_loans_on_exit_for(&self, n: &Node<'a>) -> String {
        let mut suffix = "{".to_string();
        let cfgidx = n.val0();
        let mut saw_suffix = false;
        let loans = &self.analysis_data.loans;
        if loans.has_bitset_for_cfgidx(cfgidx) {
            loans.each_bit_on_exit_frozen(cfgidx, |index| {
                let lp = self.loan_index_to_path(index);
                self.append_loan(&*lp, saw_suffix, &mut suffix);
                saw_suffix = true;
                true
            });
        }
        suffix.append("}")
    }

    fn dataflow_moves_on_exit_for(&self, n: &Node<'a>) -> String {
        let mut suffix = "{".to_string();
        let cfgidx = n.val0();
        let mut saw_suffix = false;
        let moves = &self.analysis_data.move_data.dfcx_moves;
        if moves.has_bitset_for_cfgidx(cfgidx) {
            moves.each_bit_on_exit_frozen(cfgidx, |index| {
                let lp = self.move_index_to_path(index);
                self.append_loan(&*lp, saw_suffix, &mut suffix);
                saw_suffix = true;
                true
            });
        }
        suffix.append("}")
    }

    fn dataflow_assigns_on_exit_for(&self, n: &Node<'a>) -> String {
        let mut suffix = "{".to_string();
        let cfgidx = n.val0();
        let mut saw_suffix = false;
        let move_data = &self.analysis_data.move_data;
        let assigns = &move_data.dfcx_assign;
        if assigns.has_bitset_for_cfgidx(cfgidx) {
            assigns.each_bit_on_exit_frozen(cfgidx, |index| {
                let lp = self.assign_index_to_path(index);
                self.append_loan(&*lp, saw_suffix, &mut suffix);
                saw_suffix = true;
                true
            });
        }
        suffix.append("}")
    }

    fn loan_index_to_path(&self, loan_index: uint) -> Rc<LoanPath> {
        let all_loans = &self.analysis_data.all_loans;
        all_loans.get(loan_index).loan_path()
    }
    fn move_index_to_path(&self, move_index: uint) -> Rc<LoanPath> {
        let move_data = &self.analysis_data.move_data.move_data;
        let moves = move_data.moves.borrow();
        let move = moves.get(move_index);
        move_data.path_loan_path(move.path)
    }
    fn assign_index_to_path(&self, assign_index: uint) -> Rc<LoanPath> {
        let move_data = &self.analysis_data.move_data.move_data;
        let assignments = move_data.var_assignments.borrow();
        let assignment = assignments.get(assign_index);
        move_data.path_loan_path(assignment.path)
    }

    fn append_loan(&self, loan_path: &LoanPath, seen: bool, set: &mut String) {
        if seen {
            set.push_str(", ");
        }
        let loan_str = self.borrowck_ctxt.loan_path_to_str(loan_path);
        set.push_str(loan_str.as_slice());
    }
}

impl<'a> dot::Labeller<'a, Node<'a>, Edge<'a>> for DataflowLabeller<'a> {
    fn graph_id(&'a self) -> dot::Id<'a> { self.inner.graph_id() }
    fn node_id(&'a self, n: &Node<'a>) -> dot::Id<'a> { self.inner.node_id(n) }
    fn node_label(&'a self, n: &Node<'a>) -> dot::LabelText<'a> {
        let prefix = self.dataflow_prefix_for(n);
        let suffix = self.dataflow_suffix_for(n);
        let inner_label = self.inner.node_label(n);
        inner_label
            .prefix_line(dot::LabelStr(str::Owned(prefix)))
            .suffix_line(dot::LabelStr(str::Owned(suffix)))
    }
    fn edge_label(&'a self, e: &Edge<'a>) -> dot::LabelText<'a> { self.inner.edge_label(e) }
}

impl<'a> dot::GraphWalk<'a, Node<'a>, Edge<'a>> for DataflowLabeller<'a> {
    fn nodes(&self) -> dot::Nodes<'a, Node<'a>> { self.inner.nodes() }
    fn edges(&self) -> dot::Edges<'a, Edge<'a>> { self.inner.edges() }
    fn source(&self, edge: &Edge<'a>) -> Node<'a> { self.inner.source(edge) }
    fn target(&self, edge: &Edge<'a>) -> Node<'a> { self.inner.target(edge) }
}
