// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
Managing the scope stack. The scopes are tied to lexical scopes, so as
we descend the HAIR, we push a scope on the stack, translate ite
contents, and then pop it off. Every scope is named by a
`region::Scope`.

### SEME Regions

When pushing a new scope, we record the current point in the graph (a
basic block); this marks the entry to the scope. We then generate more
stuff in the control-flow graph. Whenever the scope is exited, either
via a `break` or `return` or just by fallthrough, that marks an exit
from the scope. Each lexical scope thus corresponds to a single-entry,
multiple-exit (SEME) region in the control-flow graph.

For now, we keep a mapping from each `region::Scope` to its
corresponding SEME region for later reference (see caveat in next
paragraph). This is because region scopes are tied to
them. Eventually, when we shift to non-lexical lifetimes, there should
be no need to remember this mapping.

There is one additional wrinkle, actually, that I wanted to hide from
you but duty compels me to mention. In the course of translating
matches, it sometimes happen that certain code (namely guards) gets
executed multiple times. This means that the scope lexical scope may
in fact correspond to multiple, disjoint SEME regions. So in fact our
mapping is from one scope to a vector of SEME regions.

### Drops

The primary purpose for scopes is to insert drops: while translating
the contents, we also accumulate lvalues that need to be dropped upon
exit from each scope. This is done by calling `schedule_drop`. Once a
drop is scheduled, whenever we branch out we will insert drops of all
those lvalues onto the outgoing edge. Note that we don't know the full
set of scheduled drops up front, and so whenever we exit from the
scope we only drop the values scheduled thus far. For example, consider
the scope S corresponding to this loop:

```
# let cond = true;
loop {
    let x = ..;
    if cond { break; }
    let y = ..;
}
```

When processing the `let x`, we will add one drop to the scope for
`x`.  The break will then insert a drop for `x`. When we process `let
y`, we will add another drop (in fact, to a subscope, but let's ignore
that for now); any later drops would also drop `y`.

### Early exit

There are numerous "normal" ways to early exit a scope: `break`,
`continue`, `return` (panics are handled separately). Whenever an
early exit occurs, the method `exit_scope` is called. It is given the
current point in execution where the early exit occurs, as well as the
scope you want to branch to (note that all early exits from to some
other enclosing scope). `exit_scope` will record this exit point and
also add all drops.

Panics are handled in a similar fashion, except that a panic always
returns out to the `DIVERGE_BLOCK`. To trigger a panic, simply call
`panic(p)` with the current point `p`. Or else you can call
`diverge_cleanup`, which will produce a block that you can branch to
which does the appropriate cleanup and then diverges. `panic(p)`
simply calls `diverge_cleanup()` and adds an edge from `p` to the
result.

### Loop scopes

In addition to the normal scope stack, we track a loop scope stack
that contains only loops. It tracks where a `break` and `continue`
should go to.

*/

use build::{BlockAnd, BlockAndExtension, Builder, CFG};
use hair::LintLevel;
use rustc::middle::region;
use rustc::ty::{Ty, TyCtxt};
use rustc::hir::def_id::LOCAL_CRATE;
use rustc::mir::*;
use rustc::mir::transform::MirSource;
use syntax_pos::{Span};
use rustc_data_structures::indexed_vec::Idx;
use rustc_data_structures::fx::FxHashMap;

#[derive(Debug)]
pub struct Scope<'tcx> {
    /// The visibility scope this scope was created in.
    visibility_scope: VisibilityScope,

    /// the region span of this scope within source code.
    region_scope: region::Scope,

    /// the span of that region_scope
    region_scope_span: Span,

    /// Whether there's anything to do for the cleanup path, that is,
    /// when unwinding through this scope. This includes destructors,
    /// but not StorageDead statements, which don't get emitted at all
    /// for unwinding, for several reasons:
    ///  * clang doesn't emit llvm.lifetime.end for C++ unwinding
    ///  * LLVM's memory dependency analysis can't handle it atm
    ///  * polluting the cleanup MIR with StorageDead creates
    ///    landing pads even though there's no actual destructors
    ///  * freeing up stack space has no effect during unwinding
    needs_cleanup: bool,

    /// set of lvalues to drop when exiting this scope. This starts
    /// out empty but grows as variables are declared during the
    /// building process. This is a stack, so we always drop from the
    /// end of the vector (top of the stack) first.
    drops: Vec<DropData<'tcx>>,

    /// The cache for drop chain on “normal” exit into a particular BasicBlock.
    cached_exits: FxHashMap<(BasicBlock, region::Scope), BasicBlock>,

    /// When filled, this is the block to follow for the unwind path
    /// from this scope. (If EndRegion emission is off, then this is
    /// the same as the first filled `cached_block.unwind` (if any) on
    /// the `self.drops` stack. But in the general case we might have
    /// some EndRegion statements that take effect first, before we
    /// jump into the drop chain.)
    unwind: Option<BasicBlock>,

    /// The cache for drop chain on "generator drop" exit.
    cached_generator_drop: Option<BasicBlock>,
}

#[derive(Debug)]
struct DropData<'tcx> {
    /// span where drop obligation was incurred (typically where lvalue was declared)
    span: Span,

    /// lvalue to drop
    location: Lvalue<'tcx>,

    /// Whether this is a full value Drop, or just a StorageDead.
    kind: DropKind
}

#[derive(Debug, Default, Clone, Copy)]
struct CachedBlock {
    /// The cached block for the cleanups-on-diverge path. This block
    /// contains code to run the current drop and all the preceding
    /// drops (i.e. those having lower index in Drop’s Scope drop
    /// array)
    unwind: Option<BasicBlock>,

    /// The cached block for unwinds during cleanups-on-generator-drop path
    generator_drop: Option<BasicBlock>,
}

#[derive(Debug)]
enum DropKind {
    Value {
        cached_block: CachedBlock,
    },
    Storage
}

#[derive(Clone, Debug)]
pub struct BreakableScope<'tcx> {
    /// Region scope of the loop
    pub region_scope: region::Scope,
    /// Where the body of the loop begins. `None` if block
    pub continue_block: Option<BasicBlock>,
    /// Block to branch into when the loop or block terminates (either by being `break`-en out
    /// from, or by having its condition to become false)
    pub break_block: BasicBlock,
    /// The destination of the loop/block expression itself (i.e. where to put the result of a
    /// `break` expression)
    pub break_destination: Lvalue<'tcx>,
}

impl CachedBlock {
    fn invalidate(&mut self) {
        self.generator_drop = None;
        self.unwind = None;
    }

    fn get(&self, generator_drop: bool) -> Option<BasicBlock> {
        if generator_drop {
            self.generator_drop
        } else {
            self.unwind
        }
    }

    fn ref_mut(&mut self, generator_drop: bool) -> &mut Option<BasicBlock> {
        if generator_drop {
            &mut self.generator_drop
        } else {
            &mut self.unwind
        }
    }
}

impl DropKind {
    fn may_panic(&self) -> bool {
        match *self {
            DropKind::Value { .. } => true,
            DropKind::Storage => false
        }
    }
}

impl<'tcx> Scope<'tcx> {
    /// Invalidate all the cached blocks in the scope.
    ///
    /// Should always be run for all inner scopes when a drop is pushed into some scope enclosing a
    /// larger extent of code.
    ///
    /// `unwind` controls whether caches for the unwind branch are also invalidated.
    fn invalidate_cache(&mut self, unwind: bool) {
        debug!("invalidate_cache(unwind: {}) for Scope: {:?}", unwind, self);
        self.cached_exits.clear();
        if !unwind { return; }
        self.unwind = None;
        for dropdata in &mut self.drops {
            if let DropKind::Value { ref mut cached_block } = dropdata.kind {
                cached_block.invalidate();
            }
        }
    }

    /// Returns the cached entrypoint for diverging exit from this scope.
    ///
    /// Precondition: the caches must be fully filled (i.e. diverge_cleanup is called) in order for
    /// this method to work correctly.
    fn cached_block(&self, generator_drop: bool) -> Option<BasicBlock> {
        let mut drops = self.drops.iter().rev().filter_map(|data| {
            match data.kind {
                DropKind::Value { cached_block } => {
                    Some(cached_block.get(generator_drop))
                }
                DropKind::Storage => None
            }
        });
        if let Some(cached_block) = drops.next() {
            Some(cached_block.expect("drop cache is not filled"))
        } else {
            None
        }
    }

    /// Given a span and this scope's visibility scope, make a SourceInfo.
    fn source_info(&self, span: Span) -> SourceInfo {
        SourceInfo {
            span,
            scope: self.visibility_scope
        }
    }
}

impl<'a, 'gcx, 'tcx> Builder<'a, 'gcx, 'tcx> {
    // Adding and removing scopes
    // ==========================
    /// Start a breakable scope, which tracks where `continue` and `break`
    /// should branch to. See module comment for more details.
    ///
    /// Returns the might_break attribute of the BreakableScope used.
    pub fn in_breakable_scope<F, R>(&mut self,
                                    loop_block: Option<BasicBlock>,
                                    break_block: BasicBlock,
                                    break_destination: Lvalue<'tcx>,
                                    f: F) -> R
        where F: FnOnce(&mut Builder<'a, 'gcx, 'tcx>) -> R
    {
        let region_scope = self.topmost_scope();
        let scope = BreakableScope {
            region_scope,
            continue_block: loop_block,
            break_block,
            break_destination,
        };
        self.breakable_scopes.push(scope);
        let res = f(self);
        let breakable_scope = self.breakable_scopes.pop().unwrap();
        assert!(breakable_scope.region_scope == region_scope);
        res
    }

    pub fn in_opt_scope<F, R>(&mut self,
                              opt_scope: Option<(region::Scope, SourceInfo)>,
                              mut block: BasicBlock,
                              f: F)
                              -> BlockAnd<R>
        where F: FnOnce(&mut Builder<'a, 'gcx, 'tcx>) -> BlockAnd<R>
    {
        debug!("in_opt_scope(opt_scope={:?}, block={:?})", opt_scope, block);
        if let Some(region_scope) = opt_scope { self.push_scope(region_scope); }
        let rv = unpack!(block = f(self));
        if let Some(region_scope) = opt_scope {
            unpack!(block = self.pop_scope(region_scope, block));
        }
        debug!("in_scope: exiting opt_scope={:?} block={:?}", opt_scope, block);
        block.and(rv)
    }

    /// Convenience wrapper that pushes a scope and then executes `f`
    /// to build its contents, popping the scope afterwards.
    pub fn in_scope<F, R>(&mut self,
                          region_scope: (region::Scope, SourceInfo),
                          lint_level: LintLevel,
                          mut block: BasicBlock,
                          f: F)
                          -> BlockAnd<R>
        where F: FnOnce(&mut Builder<'a, 'gcx, 'tcx>) -> BlockAnd<R>
    {
        debug!("in_scope(region_scope={:?}, block={:?})", region_scope, block);
        let visibility_scope = self.visibility_scope;
        let tcx = self.hir.tcx();
        if let LintLevel::Explicit(node_id) = lint_level {
            let same_lint_scopes = tcx.dep_graph.with_ignore(|| {
                let sets = tcx.lint_levels(LOCAL_CRATE);
                let parent_hir_id =
                    tcx.hir.definitions().node_to_hir_id(
                        self.visibility_scope_info[visibility_scope].lint_root
                            );
                let current_hir_id =
                    tcx.hir.definitions().node_to_hir_id(node_id);
                sets.lint_level_set(parent_hir_id) ==
                    sets.lint_level_set(current_hir_id)
            });

            if !same_lint_scopes {
                self.visibility_scope =
                    self.new_visibility_scope(region_scope.1.span, lint_level,
                                              None);
            }
        }
        self.push_scope(region_scope);
        let rv = unpack!(block = f(self));
        unpack!(block = self.pop_scope(region_scope, block));
        self.visibility_scope = visibility_scope;
        debug!("in_scope: exiting region_scope={:?} block={:?}", region_scope, block);
        block.and(rv)
    }

    /// Push a scope onto the stack. You can then build code in this
    /// scope and call `pop_scope` afterwards. Note that these two
    /// calls must be paired; using `in_scope` as a convenience
    /// wrapper maybe preferable.
    pub fn push_scope(&mut self, region_scope: (region::Scope, SourceInfo)) {
        debug!("push_scope({:?})", region_scope);
        let vis_scope = self.visibility_scope;
        self.scopes.push(Scope {
            visibility_scope: vis_scope,
            region_scope: region_scope.0,
            region_scope_span: region_scope.1.span,
            needs_cleanup: false,
            drops: vec![],
            unwind: None,
            cached_generator_drop: None,
            cached_exits: FxHashMap()
        });
    }

    /// Pops a scope, which should have region scope `region_scope`,
    /// adding any drops onto the end of `block` that are needed.
    /// This must match 1-to-1 with `push_scope`.
    pub fn pop_scope(&mut self,
                     region_scope: (region::Scope, SourceInfo),
                     mut block: BasicBlock)
                     -> BlockAnd<()> {
        debug!("pop_scope({:?}, {:?})", region_scope, block);
        // If we are emitting a `drop` statement, we need to have the cached
        // diverge cleanup pads ready in case that drop panics.
        let may_panic =
            self.scopes.last().unwrap().drops.iter().any(|s| s.kind.may_panic());
        if may_panic {
            self.diverge_cleanup();
        }
        let scope = self.scopes.pop().unwrap();
        assert_eq!(scope.region_scope, region_scope.0);

        self.cfg.push_end_region(self.hir.tcx(), block, region_scope.1, scope.region_scope);
        unpack!(block = build_scope_drops(&mut self.cfg,
                                          &scope,
                                          &self.scopes,
                                          block,
                                          self.arg_count,
                                          false));

        block.unit()
    }


    /// Branch out of `block` to `target`, exiting all scopes up to
    /// and including `region_scope`.  This will insert whatever drops are
    /// needed, as well as tracking this exit for the SEME region. See
    /// module comment for details.
    pub fn exit_scope(&mut self,
                      span: Span,
                      region_scope: (region::Scope, SourceInfo),
                      mut block: BasicBlock,
                      target: BasicBlock) {
        debug!("exit_scope(region_scope={:?}, block={:?}, target={:?})",
               region_scope, block, target);
        let scope_count = 1 + self.scopes.iter().rev()
            .position(|scope| scope.region_scope == region_scope.0)
            .unwrap_or_else(|| {
                span_bug!(span, "region_scope {:?} does not enclose", region_scope)
            });
        let len = self.scopes.len();
        assert!(scope_count < len, "should not use `exit_scope` to pop ALL scopes");

        // If we are emitting a `drop` statement, we need to have the cached
        // diverge cleanup pads ready in case that drop panics.
        let may_panic = self.scopes[(len - scope_count)..].iter()
            .any(|s| s.drops.iter().any(|s| s.kind.may_panic()));
        if may_panic {
            self.diverge_cleanup();
        }

        {
        let mut rest = &mut self.scopes[(len - scope_count)..];
        while let Some((scope, rest_)) = {rest}.split_last_mut() {
            rest = rest_;
            block = if let Some(&e) = scope.cached_exits.get(&(target, region_scope.0)) {
                self.cfg.terminate(block, scope.source_info(span),
                                   TerminatorKind::Goto { target: e });
                return;
            } else {
                let b = self.cfg.start_new_block();
                self.cfg.terminate(block, scope.source_info(span),
                                   TerminatorKind::Goto { target: b });
                scope.cached_exits.insert((target, region_scope.0), b);
                b
            };

            // End all regions for scopes out of which we are breaking.
            self.cfg.push_end_region(self.hir.tcx(), block, region_scope.1, scope.region_scope);

            unpack!(block = build_scope_drops(&mut self.cfg,
                                              scope,
                                              rest,
                                              block,
                                              self.arg_count,
                                              false));
        }
        }
        let scope = &self.scopes[len - scope_count];
        self.cfg.terminate(block, scope.source_info(span),
                           TerminatorKind::Goto { target: target });
    }

    /// Creates a path that performs all required cleanup for dropping a generator.
    ///
    /// This path terminates in GeneratorDrop. Returns the start of the path.
    /// None indicates there’s no cleanup to do at this point.
    pub fn generator_drop_cleanup(&mut self) -> Option<BasicBlock> {
        if !self.scopes.iter().any(|scope| scope.needs_cleanup) {
            return None;
        }

        // Fill in the cache
        self.diverge_cleanup_gen(true);

        let src_info = self.scopes[0].source_info(self.fn_span);
        let mut block = self.cfg.start_new_block();
        let result = block;
        let mut rest = &mut self.scopes[..];

        while let Some((scope, rest_)) = {rest}.split_last_mut() {
            rest = rest_;
            if !scope.needs_cleanup {
                continue;
            }
            block = if let Some(b) = scope.cached_generator_drop {
                self.cfg.terminate(block, src_info,
                                   TerminatorKind::Goto { target: b });
                return Some(result);
            } else {
                let b = self.cfg.start_new_block();
                scope.cached_generator_drop = Some(b);
                self.cfg.terminate(block, src_info,
                                   TerminatorKind::Goto { target: b });
                b
            };
            unpack!(block = build_scope_drops(&mut self.cfg,
                                              scope,
                                              rest,
                                              block,
                                              self.arg_count,
                                              true));

            // End all regions for scopes out of which we are breaking.
            self.cfg.push_end_region(self.hir.tcx(), block, src_info, scope.region_scope);
        }

        self.cfg.terminate(block, src_info, TerminatorKind::GeneratorDrop);

        Some(result)
    }

    /// Creates a new visibility scope, nested in the current one.
    pub fn new_visibility_scope(&mut self,
                                span: Span,
                                lint_level: LintLevel,
                                safety: Option<Safety>) -> VisibilityScope {
        let parent = self.visibility_scope;
        debug!("new_visibility_scope({:?}, {:?}, {:?}) - parent({:?})={:?}",
               span, lint_level, safety,
               parent, self.visibility_scope_info.get(parent));
        let scope = self.visibility_scopes.push(VisibilityScopeData {
            span,
            parent_scope: Some(parent),
        });
        let scope_info = VisibilityScopeInfo {
            lint_root: if let LintLevel::Explicit(lint_root) = lint_level {
                lint_root
            } else {
                self.visibility_scope_info[parent].lint_root
            },
            safety: safety.unwrap_or_else(|| {
                self.visibility_scope_info[parent].safety
            })
        };
        self.visibility_scope_info.push(scope_info);
        scope
    }

    // Finding scopes
    // ==============
    /// Finds the breakable scope for a given label. This is used for
    /// resolving `break` and `continue`.
    pub fn find_breakable_scope(&mut self,
                           span: Span,
                           label: region::Scope)
                           -> &mut BreakableScope<'tcx> {
        // find the loop-scope with the correct id
        self.breakable_scopes.iter_mut()
            .rev()
            .filter(|breakable_scope| breakable_scope.region_scope == label)
            .next()
            .unwrap_or_else(|| span_bug!(span, "no enclosing breakable scope found"))
    }

    /// Given a span and the current visibility scope, make a SourceInfo.
    pub fn source_info(&self, span: Span) -> SourceInfo {
        SourceInfo {
            span,
            scope: self.visibility_scope
        }
    }

    /// Returns the `region::Scope` of the scope which should be exited by a
    /// return.
    pub fn region_scope_of_return_scope(&self) -> region::Scope {
        // The outermost scope (`scopes[0]`) will be the `CallSiteScope`.
        // We want `scopes[1]`, which is the `ParameterScope`.
        assert!(self.scopes.len() >= 2);
        assert!(match self.scopes[1].region_scope.data() {
            region::ScopeData::Arguments(_) => true,
            _ => false,
        });
        self.scopes[1].region_scope
    }

    /// Returns the topmost active scope, which is known to be alive until
    /// the next scope expression.
    pub fn topmost_scope(&self) -> region::Scope {
        self.scopes.last().expect("topmost_scope: no scopes present").region_scope
    }

    /// Returns the scope that we should use as the lifetime of an
    /// operand. Basically, an operand must live until it is consumed.
    /// This is similar to, but not quite the same as, the temporary
    /// scope (which can be larger or smaller).
    ///
    /// Consider:
    ///
    ///     let x = foo(bar(X, Y));
    ///
    /// We wish to pop the storage for X and Y after `bar()` is
    /// called, not after the whole `let` is completed.
    ///
    /// As another example, if the second argument diverges:
    ///
    ///     foo(Box::new(2), panic!())
    ///
    /// We would allocate the box but then free it on the unwinding
    /// path; we would also emit a free on the 'success' path from
    /// panic, but that will turn out to be removed as dead-code.
    ///
    /// When building statics/constants, returns `None` since
    /// intermediate values do not have to be dropped in that case.
    pub fn local_scope(&self) -> Option<region::Scope> {
        match self.hir.src {
            MirSource::Const(_) |
            MirSource::Static(..) =>
                // No need to free storage in this context.
                None,
            MirSource::Fn(_) =>
                Some(self.topmost_scope()),
            MirSource::Promoted(..) |
            MirSource::GeneratorDrop(..) =>
                bug!(),
        }
    }

    // Scheduling drops
    // ================
    /// Indicates that `lvalue` should be dropped on exit from
    /// `region_scope`.
    pub fn schedule_drop(&mut self,
                         span: Span,
                         region_scope: region::Scope,
                         lvalue: &Lvalue<'tcx>,
                         lvalue_ty: Ty<'tcx>) {
        let needs_drop = self.hir.needs_drop(lvalue_ty);
        let drop_kind = if needs_drop {
            DropKind::Value { cached_block: CachedBlock::default() }
        } else {
            // Only temps and vars need their storage dead.
            match *lvalue {
                Lvalue::Local(index) if index.index() > self.arg_count => DropKind::Storage,
                _ => return
            }
        };

        for scope in self.scopes.iter_mut().rev() {
            let this_scope = scope.region_scope == region_scope;
            // When building drops, we try to cache chains of drops in such a way so these drops
            // could be reused by the drops which would branch into the cached (already built)
            // blocks.  This, however, means that whenever we add a drop into a scope which already
            // had some blocks built (and thus, cached) for it, we must invalidate all caches which
            // might branch into the scope which had a drop just added to it. This is necessary,
            // because otherwise some other code might use the cache to branch into already built
            // chain of drops, essentially ignoring the newly added drop.
            //
            // For example consider there’s two scopes with a drop in each. These are built and
            // thus the caches are filled:
            //
            // +--------------------------------------------------------+
            // | +---------------------------------+                    |
            // | | +--------+     +-------------+  |  +---------------+ |
            // | | | return | <-+ | drop(outer) | <-+ |  drop(middle) | |
            // | | +--------+     +-------------+  |  +---------------+ |
            // | +------------|outer_scope cache|--+                    |
            // +------------------------------|middle_scope cache|------+
            //
            // Now, a new, inner-most scope is added along with a new drop into both inner-most and
            // outer-most scopes:
            //
            // +------------------------------------------------------------+
            // | +----------------------------------+                       |
            // | | +--------+      +-------------+  |   +---------------+   | +-------------+
            // | | | return | <+   | drop(new)   | <-+  |  drop(middle) | <--+| drop(inner) |
            // | | +--------+  |   | drop(outer) |  |   +---------------+   | +-------------+
            // | |             +-+ +-------------+  |                       |
            // | +---|invalid outer_scope cache|----+                       |
            // +----=----------------|invalid middle_scope cache|-----------+
            //
            // If, when adding `drop(new)` we do not invalidate the cached blocks for both
            // outer_scope and middle_scope, then, when building drops for the inner (right-most)
            // scope, the old, cached blocks, without `drop(new)` will get used, producing the
            // wrong results.
            //
            // The cache and its invalidation for unwind branch is somewhat special. The cache is
            // per-drop, rather than per scope, which has a several different implications. Adding
            // a new drop into a scope will not invalidate cached blocks of the prior drops in the
            // scope. That is true, because none of the already existing drops will have an edge
            // into a block with the newly added drop.
            //
            // Note that this code iterates scopes from the inner-most to the outer-most,
            // invalidating caches of each scope visited. This way bare minimum of the
            // caches gets invalidated. i.e. if a new drop is added into the middle scope, the
            // cache of outer scpoe stays intact.
            let invalidate_unwind = needs_drop && !this_scope;
            scope.invalidate_cache(invalidate_unwind);
            if this_scope {
                if let DropKind::Value { .. } = drop_kind {
                    scope.needs_cleanup = true;
                }
                let region_scope_span = region_scope.span(self.hir.tcx(),
                                                          &self.hir.region_scope_tree);
                // Attribute scope exit drops to scope's closing brace
                let scope_end = region_scope_span.with_lo(region_scope_span.hi());
                scope.drops.push(DropData {
                    span: scope_end,
                    location: lvalue.clone(),
                    kind: drop_kind
                });
                return;
            }
        }
        span_bug!(span, "region scope {:?} not in scope to drop {:?}", region_scope, lvalue);
    }

    // Other
    // =====
    /// Creates a path that performs all required cleanup for unwinding.
    ///
    /// This path terminates in Resume. Returns the start of the path.
    /// See module comment for more details. None indicates there’s no
    /// cleanup to do at this point.
    pub fn diverge_cleanup(&mut self) -> Option<BasicBlock> {
        self.diverge_cleanup_gen(false)
    }

    fn diverge_cleanup_gen(&mut self, generator_drop: bool) -> Option<BasicBlock> {
        if !self.scopes.iter().any(|scope| scope.needs_cleanup) {
            return None;
        }
        assert!(!self.scopes.is_empty()); // or `any` above would be false

        let Builder { ref mut cfg, ref mut scopes,
                      ref mut cached_resume_block, .. } = *self;

        // Build up the drops in **reverse** order. The end result will
        // look like:
        //
        //    scopes[n] -> scopes[n-1] -> ... -> scopes[0]
        //
        // However, we build this in **reverse order**. That is, we
        // process scopes[0], then scopes[1], etc, pointing each one at
        // the result generates from the one before. Along the way, we
        // store caches. If everything is cached, we'll just walk right
        // to left reading the cached results but never created anything.

        // To start, create the resume terminator.
        let mut target = if let Some(target) = *cached_resume_block {
            target
        } else {
            let resumeblk = cfg.start_new_cleanup_block();
            cfg.terminate(resumeblk,
                          scopes[0].source_info(self.fn_span),
                          TerminatorKind::Resume);
            *cached_resume_block = Some(resumeblk);
            resumeblk
        };

        for scope in scopes.iter_mut() {
            target = build_diverge_scope(self.hir.tcx(), cfg, scope.region_scope_span,
                                         scope, target, generator_drop);
        }
        Some(target)
    }

    /// Utility function for *non*-scope code to build their own drops
    pub fn build_drop(&mut self,
                      block: BasicBlock,
                      span: Span,
                      location: Lvalue<'tcx>,
                      ty: Ty<'tcx>) -> BlockAnd<()> {
        if !self.hir.needs_drop(ty) {
            return block.unit();
        }
        let source_info = self.source_info(span);
        let next_target = self.cfg.start_new_block();
        let diverge_target = self.diverge_cleanup();
        self.cfg.terminate(block, source_info,
                           TerminatorKind::Drop {
                               location,
                               target: next_target,
                               unwind: diverge_target,
                           });
        next_target.unit()
    }

    /// Utility function for *non*-scope code to build their own drops
    pub fn build_drop_and_replace(&mut self,
                                  block: BasicBlock,
                                  span: Span,
                                  location: Lvalue<'tcx>,
                                  value: Operand<'tcx>) -> BlockAnd<()> {
        let source_info = self.source_info(span);
        let next_target = self.cfg.start_new_block();
        let diverge_target = self.diverge_cleanup();
        self.cfg.terminate(block, source_info,
                           TerminatorKind::DropAndReplace {
                               location,
                               value,
                               target: next_target,
                               unwind: diverge_target,
                           });
        next_target.unit()
    }

    /// Create an Assert terminator and return the success block.
    /// If the boolean condition operand is not the expected value,
    /// a runtime panic will be caused with the given message.
    pub fn assert(&mut self, block: BasicBlock,
                  cond: Operand<'tcx>,
                  expected: bool,
                  msg: AssertMessage<'tcx>,
                  span: Span)
                  -> BasicBlock {
        let source_info = self.source_info(span);

        let success_block = self.cfg.start_new_block();
        let cleanup = self.diverge_cleanup();

        self.cfg.terminate(block, source_info,
                           TerminatorKind::Assert {
                               cond,
                               expected,
                               msg,
                               target: success_block,
                               cleanup,
                           });

        success_block
    }
}

/// Builds drops for pop_scope and exit_scope.
fn build_scope_drops<'tcx>(cfg: &mut CFG<'tcx>,
                           scope: &Scope<'tcx>,
                           earlier_scopes: &[Scope<'tcx>],
                           mut block: BasicBlock,
                           arg_count: usize,
                           generator_drop: bool)
                           -> BlockAnd<()> {
    debug!("build_scope_drops({:?} -> {:?}); earlier_scopes: {:?}",
           block, scope, earlier_scopes);
    let mut iter = scope.drops.iter().rev().peekable();
    while let Some(drop_data) = iter.next() {
        let source_info = scope.source_info(drop_data.span);
        debug!("build_scope_drops while let drop_data: {:?}", drop_data);
        match drop_data.kind {
            DropKind::Value { .. } => {
                // Try to find the next block with its cached block
                // for us to diverge into in case the drop panics.
                let on_diverge = iter.peek().iter().filter_map(|dd| {
                    match dd.kind {
                        DropKind::Value { cached_block } => {
                            let result = cached_block.get(generator_drop);
                            if result.is_none() {
                                span_bug!(drop_data.span, "cached block not present?")
                            }
                            result
                        },
                        DropKind::Storage => None
                    }
                }).next();
                debug!("build_scope_drops peeked on_diverge: {:?}", on_diverge);
                // If there’s no `cached_block`s within current scope,
                // we must look for one in the enclosing scope.
                let on_diverge = on_diverge.or_else(|| {
                    earlier_scopes.iter().rev().flat_map(|s| s.cached_block(generator_drop)).next()
                });
                debug!("build_scope_drops earlier_scopes on_diverge: {:?}", on_diverge);
                let next = cfg.start_new_block();
                cfg.terminate(block, source_info, TerminatorKind::Drop {
                    location: drop_data.location.clone(),
                    target: next,
                    unwind: on_diverge
                });
                block = next;
            }
            DropKind::Storage => {}
        }

        // We do not need to emit StorageDead for generator drops
        if generator_drop {
            continue
        }

        // Drop the storage for both value and storage drops.
        // Only temps and vars need their storage dead.
        match drop_data.location {
            Lvalue::Local(index) if index.index() > arg_count => {
                cfg.push(block, Statement {
                    source_info,
                    kind: StatementKind::StorageDead(index)
                });
            }
            _ => continue
        }
    }
    block.unit()
}

fn build_diverge_scope<'a, 'gcx, 'tcx>(tcx: TyCtxt<'a, 'gcx, 'tcx>,
                                       cfg: &mut CFG<'tcx>,
                                       span: Span,
                                       scope: &mut Scope<'tcx>,
                                       mut target: BasicBlock,
                                       generator_drop: bool)
                                       -> BasicBlock
{
    assert!(scope.unwind.is_none());

    // Build up the drops in **reverse** order. The end result will
    // look like:
    //
    //    [EndRegion Block] -> [drops[n]] -...-> [drops[0]] -> [Free] -> [target]
    //    |                                                         |
    //    +---------------------------------------------------------+
    //     code for scope
    //
    // The code in this function reads from right to left. At each
    // point, we check for cached blocks representing the
    // remainder. If everything is cached, we'll just walk right to
    // left reading the cached results but never create anything.

    let visibility_scope = scope.visibility_scope;
    let source_info = |span| SourceInfo {
        span,
        scope: visibility_scope
    };

    // Next, build up the drops. Here we iterate the vector in
    // *forward* order, so that we generate drops[0] first (right to
    // left in diagram above).
    for (j, drop_data) in scope.drops.iter_mut().enumerate() {
        debug!("build_diverge_scope drop_data[{}]: {:?}", j, drop_data);
        // Only full value drops are emitted in the diverging path,
        // not StorageDead.
        //
        // Note: This may not actually be what we desire (are we
        // "freeing" stack storage as we unwind, or merely observing a
        // frozen stack)? In particular, the intent may have been to
        // match the behavior of clang, but on inspection eddyb says
        // this is not what clang does.
        let cached_block = match drop_data.kind {
            DropKind::Value { ref mut cached_block } => cached_block.ref_mut(generator_drop),
            DropKind::Storage => continue
        };
        target = if let Some(cached_block) = *cached_block {
            cached_block
        } else {
            let block = cfg.start_new_cleanup_block();
            cfg.terminate(block, source_info(drop_data.span),
                          TerminatorKind::Drop {
                              location: drop_data.location.clone(),
                              target,
                              unwind: None
                          });

            *cached_block = Some(block);
            block
        };
    }

    // Finally, push the EndRegion statement, used by mir-borrowck.
    //
    // If we created a fresh block above, then put the EndRegion there
    // to ensure that the statement is part of the unwind chain of
    // blocks held in `cached_block`. If we didn't create a fresh
    // block (i.e. there were no uncached blocks holding
    // DropKind::Value's to drop), then make a fresh block here for
    // the EndRegion. Either way the EndRegion will be replaced with a
    // no-op after mir-borrowck runs.
    {
        let block = cfg.start_new_cleanup_block();
        cfg.push_end_region(tcx, block, source_info(span), scope.region_scope);
        cfg.terminate(block, source_info(span), TerminatorKind::Goto { target: target });
        target = block;
        scope.unwind = Some(target);
    }

    debug!("build_diverge_scope scope: {:?} now has unwind target: {:?}", scope, target);

    target
}
