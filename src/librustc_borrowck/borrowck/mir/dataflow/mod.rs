// Copyright 2012-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc_mir::dataflow::{BitDenotation, Dataflow};
use std::fmt::Debug;
use std::io;
use std::path::PathBuf;

use super::MirBorrowckCtxtPreDataflow;

pub use self::sanity_check::sanity_check_via_rustc_peek;
pub use self::impls::{MaybeInitializedLvals, MaybeUninitializedLvals};
pub use self::impls::{DefinitelyInitializedLvals, MovingOutStatements};
pub use self::impls::{Borrows, BorrowData};

mod graphviz;
mod sanity_check;
mod impls;

impl<'a, 'tcx: 'a, BD> Dataflow<BD> for MirBorrowckCtxtPreDataflow<'a, 'tcx, BD>
    where BD: BitDenotation
{
    fn dataflow<P>(&mut self, p: P) where P: Fn(&BD, BD::Idx) -> &Debug {
        self.build_sets();
        self.pre_dataflow_instrumentation(|c,i| p(c,i)).unwrap();
        self.propagate();
        self.post_dataflow_instrumentation(|c,i| p(c,i)).unwrap();
    }

    fn build_sets(&mut self) { self.flow_state.build_sets(); }
    fn propagate(&mut self) { self.flow_state.propagate(); }
}

fn dataflow_path(context: &str, prepost: &str, path: &str) -> PathBuf {
    format!("{}_{}", context, prepost);
    let mut path = PathBuf::from(path);
    let new_file_name = {
        let orig_file_name = path.file_name().unwrap().to_str().unwrap();
        format!("{}_{}", context, orig_file_name)
    };
    path.set_file_name(new_file_name);
    path
}

impl<'a, 'tcx: 'a, BD> MirBorrowckCtxtPreDataflow<'a, 'tcx, BD>
    where BD: BitDenotation
{
    fn pre_dataflow_instrumentation<P>(&self, p: P) -> io::Result<()>
        where P: Fn(&BD, BD::Idx) -> &Debug
    {
        if let Some(ref path_str) = self.print_preflow_to {
            let path = dataflow_path(BD::name(), "preflow", path_str);
            graphviz::print_borrowck_graph_to(self, &path, p)
        } else {
            Ok(())
        }
    }

    fn post_dataflow_instrumentation<P>(&self, p: P) -> io::Result<()>
        where P: Fn(&BD, BD::Idx) -> &Debug
    {
        if let Some(ref path_str) = self.print_postflow_to {
            let path = dataflow_path(BD::name(), "postflow", path_str);
            graphviz::print_borrowck_graph_to(self, &path, p)
        } else{
            Ok(())
        }
    }
}
