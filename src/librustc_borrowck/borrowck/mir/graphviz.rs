// Copyright 2012-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Hook into libgraphviz for rendering dataflow graphs for MIR.

use rustc::mir::repr::{BasicBlock, Mir};

use dot;
use dot::IntoCow;

use std::fs::File;
use std::io;
use std::io::prelude::*;

use super::MirBorrowckCtxt;
use super::dataflow::bits_to_string;
use super::gather_moves::MoveOut;

struct Graph<'c, 'b:'c, 'a:'b, 'tcx:'a> { mbcx: &'c MirBorrowckCtxt<'b, 'a, 'tcx>,
                                          context: &'b str }

pub fn print_borrowck_graph_to(mbcx: &MirBorrowckCtxt,
                               context: &str,
                               path: &str) -> io::Result<()> {
    let g = Graph { mbcx: mbcx, context: context };
    let mut v = Vec::new();
    try!(dot::render(&g, &mut v));
    println!("print_borrowck_graph_to path: {} context: {} node_id: {}",
             path, context, mbcx.node_id);
    File::create(path).and_then(|mut f| f.write_all(&v))
}

pub type Node = BasicBlock;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Edge { source: BasicBlock, index: usize }

fn outgoing(mir: &Mir, bb: BasicBlock) -> Vec<Edge> {
    let succ_len = mir.basic_block_data(bb).terminator().successors().len();
    (0..succ_len).map(|index| Edge { source: bb, index: index}).collect()
}

impl<'c, 'b:'c, 'a:'b, 'tcx:'a> dot::Labeller<'c> for Graph<'c,'b,'a,'tcx> {
    type Node = Node;
    type Edge = Edge;
    fn graph_id(&self) -> dot::Id {
        dot::Id::new(format!("graph_for_node_{}_{}",
                             self.mbcx.node_id,
                             self.context))
            .unwrap()
    }

    fn node_id(&self, n: &Node) -> dot::Id {
        dot::Id::new(format!("bb_{}", n.index()))
            .unwrap()
    }

    fn node_label(&self, n: &Node) -> dot::LabelText {
        let mut v = Vec::new();
        let i = n.index();
        let chunk_size = 5;
        fn chunked_present_left<W:io::Write>(w: &mut W,
                                             interpreted: &[&MoveOut],
                                             chunk_size: usize)
                                             -> io::Result<()>
        {
            let mut seen_one = false;
            for c in interpreted.chunks(chunk_size) {
                if seen_one {
                    try!(write!(w, r#"</td><td></td><td></td></tr>"#));
                }
                try!(write!(w, r#"<tr><td></td><td bgcolor="pink" align="right">{OBJS:?}"#, OBJS=c));
                seen_one = true;
            }
            if !seen_one {
                try!(write!(w, r#"<tr><td></td><td bgcolor="pink" align="right">[]"#));
            }
            Ok(())
        }
        ::rustc_mir::graphviz::write_node_label(
            *n, self.mbcx.mir, &mut v, 4,
            |w| {
                let flow = &self.mbcx.flow_state;
                let entry = flow.interpret_set(flow.sets.on_entry_set_for(i));
                chunked_present_left(w, &entry[..], chunk_size);
                write!(w, r#"= ENTRY:</td><td bgcolor="pink"><FONT FACE="Courier">{ENTRYBITS:?}</FONT></td><td></td></tr>"#,
                       ENTRYBITS=bits_to_string(flow.sets.on_entry_set_for(i),
                                                flow.sets.bytes_per_block()))
            },
            |w| {
                let flow = &self.mbcx.flow_state;
                let gen = flow.interpret_set( flow.sets.gen_set_for(i));
                let kill = flow.interpret_set(flow.sets.kill_set_for(i));
                chunked_present_left(w, &gen[..], chunk_size);
                try!(write!(w, r#" = GEN:</td><td bgcolor="pink"><FONT FACE="Courier">{GENBITS:?}</FONT></td><td></td></tr>"#,
                            GENBITS=bits_to_string( flow.sets.gen_set_for(i),
                                                    flow.sets.bytes_per_block())));
                try!(write!(w, r#"<tr><td></td><td bgcolor="pink" align="right">KILL:</td><td bgcolor="pink"><FONT FACE="Courier">{KILLBITS:?}</FONT></td>"#,
                            KILLBITS=bits_to_string(flow.sets.kill_set_for(i),
                                                    flow.sets.bytes_per_block())));

                // (chunked_present_right)
                let mut seen_one = false;
                for k in kill.chunks(chunk_size) {
                    if !seen_one {
                        try!(write!(w, r#"<td bgcolor="pink">= {KILL:?}</td></tr>"#,
                                    KILL=k));
                    } else {
                        try!(write!(w, r#"<tr><td></td><td></td><td></td><td bgcolor="pink">{KILL:?}</td></tr>"#,
                                    KILL=k));
                    }
                    seen_one = true;
                }
                if !seen_one {
                    try!(write!(w, r#"<td bgcolor="pink">= []</td></tr>"#));
                }

                Ok(())
            })
            .unwrap();
        dot::LabelText::html(String::from_utf8(v).unwrap())
    }

    fn node_shape(&self, _n: &Node) -> Option<dot::LabelText> {
        Some(dot::LabelText::label("none"))
    }
}

impl<'c, 'b:'c, 'a:'b, 'tcx:'a> dot::GraphWalk<'c> for Graph<'c,'b,'a,'tcx> {
    type Node = Node;
    type Edge = Edge;
    fn nodes(&self) -> dot::Nodes<Node> {
        self.mbcx.mir.all_basic_blocks().into_cow()
    }

    fn edges(&self) -> dot::Edges<Edge> {
        let mir = self.mbcx.mir;
        let blocks = self.mbcx.mir.all_basic_blocks();
        // base initial capacity on assumption every block has at
        // least one outgoing edge (Which should be true for all
        // blocks but one, the exit-block).
        let mut edges = Vec::with_capacity(blocks.len());
        for bb in blocks {
            let outgoing = outgoing(mir, bb);
            edges.extend(outgoing.into_iter());
        }
        edges.into_cow()
    }

    fn source(&self, edge: &Edge) -> Node {
        edge.source
    }

    fn target(&self, edge: &Edge) -> Node {
        let mir = self.mbcx.mir;
        mir.basic_block_data(edge.source).terminator().successors()[edge.index]
    }
}
