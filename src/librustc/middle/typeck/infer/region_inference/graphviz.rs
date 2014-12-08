// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This module provides linkage between libgraphviz traits and
//! `rustc::middle::typeck::infer::region_inference`, generating a
//! rendering of the graph represented by the list of `Constraint`
//! instances (which make up the edges of the graph), as well as the
//! origin for each constraint (which are attached to the labels on
//! each edge).

/// For clarity, rename the graphviz crate locally to dot.
use graphviz as dot;

use middle::ty;
use super::Constraint;
use middle::typeck::infer::SubregionOrigin;
use util::nodemap::{FnvHashMap, FnvHashSet};
use util::ppaux::Repr;

use std::collections::hash_map::Vacant;
use std::io::{mod, File};

struct ConstraintGraph<'a, 'tcx: 'a> {
    tcx: &'a ty::ctxt<'tcx>,
    graph_name: String,
    map: &'a FnvHashMap<Constraint, SubregionOrigin<'tcx>>,
    node_ids: FnvHashMap<Node, uint>,
}

#[deriving(Clone, Hash, PartialEq, Eq, Show)]
enum Node {
    RegionVid(ty::RegionVid),
    Region(ty::Region),
}

type Edge = Constraint;

impl<'a, 'tcx> ConstraintGraph<'a, 'tcx> {
    fn new(tcx: &'a ty::ctxt<'tcx>,
           name: String,
           map: &'a ConstraintMap<'tcx>) -> ConstraintGraph<'a, 'tcx> {
        let mut i = 0;
        let mut node_ids = FnvHashMap::new();
        {
            let add_node = |node| {
                if let Vacant(e) = node_ids.entry(node) {
                    e.set(i);
                    i += 1;
                }
            };

            for (n1, n2) in map.keys().map(|c|constraint_to_nodes(c)) {
                add_node(n1);
                add_node(n2);
            }
        }

        ConstraintGraph { tcx: tcx,
                          graph_name: name,
                          map: map,
                          node_ids: node_ids }
    }
}

impl<'a, 'tcx> dot::Labeller<'a, Node, Edge> for ConstraintGraph<'a, 'tcx> {
    fn graph_id(&self) -> dot::Id {
        dot::Id::new(self.graph_name.as_slice()).unwrap()
    }
    fn node_id(&self, n: &Node) -> dot::Id {
        dot::Id::new(format!("node_{}", self.node_ids.get(n).unwrap())).unwrap()
    }
    fn node_label(&self, n: &Node) -> dot::LabelText {
        dot::LabelText::label(format!("{}", n))
}
    fn edge_label(&self, e: &Edge) -> dot::LabelText {
        dot::LabelText::label(format!("{}", self.map.get(e).unwrap().repr(self.tcx)))
    }
}

fn constraint_to_nodes(c: &Constraint) -> (Node, Node) {
    match *c {
        Constraint::ConstrainVarSubVar(rv_1, rv_2) => (Node::RegionVid(rv_1),
                                                       Node::RegionVid(rv_2)),
        Constraint::ConstrainRegSubVar(r_1, rv_2) => (Node::Region(r_1),
                                                      Node::RegionVid(rv_2)),
        Constraint::ConstrainVarSubReg(rv_1, r_2) => (Node::RegionVid(rv_1),
                                                      Node::Region(r_2)),
    }
}

impl<'a, 'tcx> dot::GraphWalk<'a, Node, Edge> for ConstraintGraph<'a, 'tcx> {
    fn nodes(&self) -> dot::Nodes<Node> {
        let mut set = FnvHashSet::new();
        for constraint in self.map.keys() {
            let (n1, n2) = constraint_to_nodes(constraint);
            set.insert(n1);
            set.insert(n2);
        }
        debug!("constraint graph has {} nodes", set.len());
        set.into_iter().collect()
    }
    fn edges(&self) -> dot::Edges<Edge> {
        debug!("constraint graph has {} edges", self.map.len());
        self.map.keys().map(|e|*e).collect()
    }
    fn source(&self, edge: &Edge) -> Node {
        let (n1, _) = constraint_to_nodes(edge);
        debug!("edge {} has source {}", edge, n1);
        n1
    }
    fn target(&self, edge: &Edge) -> Node {
        let (_, n2) = constraint_to_nodes(edge);
        debug!("edge {} has target {}", edge, n2);
        n2
    }
}

pub type ConstraintMap<'tcx> = FnvHashMap<Constraint, SubregionOrigin<'tcx>>;

pub fn dump_region_constraints_to<'a, 'tcx:'a >(tcx: &'a ty::ctxt<'tcx>,
                                                map: &ConstraintMap<'tcx>,
                                                path: &str) -> io::IoResult<()> {
    debug!("dump_region_constraints map (len: {}) path: {}", map.len(), path);
    let g = ConstraintGraph::new(tcx, format!("region_constraints"), map);
    let mut f = File::create(&Path::new(path));
    debug!("dump_region_constraints calling render");
    dot::render(&g, &mut f)
}
