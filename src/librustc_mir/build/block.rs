// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use build::{BlockAnd, BlockAndExtension, Builder};
use hair::*;
use rustc::mir::*;
use rustc::hir;

impl<'a, 'gcx, 'tcx> Builder<'a, 'gcx, 'tcx> {
    pub fn ast_block(&mut self,
                     destination: &Lvalue<'tcx>,
                     mut block: BasicBlock,
                     ast_block: &'tcx hir::Block)
                     -> BlockAnd<()> {
        let Block { extent, opt_destruction_extent, span, stmts, expr } =
            self.hir.mirror(ast_block);
        let source_info = self.source_info(span);
        if let Some(de) = opt_destruction_extent {
            self.push_scope(de);
        }
        let block_and = self.in_scope((extent, source_info), block, move |this| {
            // This convoluted structure is to avoid using recursion as we walk down a list
            // of statements. Basically, the structure we get back is something like:
            //
            //    let x = <init> in {
            //       expr1;
            //       let y = <init> in {
            //           expr2;
            //           expr3;
            //           ...
            //       }
            //    }
            //
            // The let bindings are valid till the end of block so all we have to do is to pop all
            // the let-scopes at the end.
            //
            // First we build all the statements in the block.
            let mut let_extent_stack = Vec::with_capacity(8);
            let outer_visibility_scope = this.visibility_scope;
            for stmt in stmts {
                let Stmt { span, kind, opt_destruction_extent } = this.hir.mirror(stmt);
                match kind {
                    StmtKind::Expr { scope, expr } => {
                        if let Some(de) = opt_destruction_extent {
                            this.push_scope(de);
                        }
                        let source_info = this.source_info(span);
                        unpack!(block = this.in_scope((scope, source_info), block, |this| {
                            let expr = this.hir.mirror(expr);
                            this.stmt_expr(block, expr)
                        }));

                        if let Some(de) = opt_destruction_extent {
                            unpack!(block = this.pop_scope((de, source_info), block));
                        }
                    }
                    StmtKind::Let { remainder_scope, init_scope, pattern, initializer } => {
                        let tcx = this.hir.tcx();

                        // Enter the remainder scope, i.e. the bindings' destruction scope.
                        let source_info = this.source_info(span);
                        this.push_scope(remainder_scope);
                        let_extent_stack.push((remainder_scope, source_info));

                        // Declare the bindings, which may create a visibility scope.
                        let remainder_span = remainder_scope.span(&tcx.region_maps, &tcx.hir);
                        let remainder_span = remainder_span.unwrap_or(span);
                        let scope = this.declare_bindings(None, remainder_span, &pattern);

                        // Evaluate the initializer, if present.
                        if let Some(init) = initializer {
                            if let Some(de) = opt_destruction_extent {
                                this.push_scope(de);
                            }

                            let init_scope = (init_scope, source_info);
                            unpack!(block = this.in_scope(init_scope, block, move |this| {
                                // FIXME #30046                              ^~~~
                                this.expr_into_pattern(block, pattern, init)
                            }));

                            if let Some(de) = opt_destruction_extent {
                                unpack!(block = this.pop_scope((de, source_info), block));
                            }
                        } else {
                            this.storage_live_for_bindings(block, &pattern);
                        }

                        // Enter the visibility scope, after evaluating the initializer.
                        if let Some(visibility_scope) = scope {
                            this.visibility_scope = visibility_scope;
                        }
                    }
                }
            }
            // Then, the block may have an optional trailing expression which is a “return” value
            // of the block.
            if let Some(expr) = expr {
                unpack!(block = this.into(destination, block, expr));
            } else {
                let source_info = this.source_info(span);
                this.cfg.push_assign_unit(block, source_info, destination);
            }
            // Finally, we pop all the let scopes before exiting out from the scope of block
            // itself.
            for (extent, source_info) in let_extent_stack.into_iter().rev() {
                unpack!(block = this.pop_scope((extent, source_info), block));
                if this.hir.seen_borrows().contains(&extent) {
                    this.cfg.push_end_region(block, source_info, extent);
                }
            }
            // Restore the original visibility scope.
            this.visibility_scope = outer_visibility_scope;
            block.unit()
        });

        if let Some(de) = opt_destruction_extent {
            self.pop_scope((de, source_info), unpack!(block_and))
        } else {
            block_and
        }
    }
}
