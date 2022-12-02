use crate::{ImplTraitContext, ImplTraitPosition, LoweringContext};
use rustc_ast::{Block, BlockCheckMode, Local, LocalKind, Stmt, StmtKind};
use rustc_hir as hir;
use rustc_span::symbol::sym;

use smallvec::SmallVec;

impl<'a, 'hir> LoweringContext<'a, 'hir> {
    pub(super) fn lower_block(
        &mut self,
        b: &Block,
        targeted_by_break: bool,
    ) -> &'hir hir::Block<'hir> {
        self.arena.alloc(self.lower_block_noalloc(b, targeted_by_break))
    }

    pub(super) fn lower_block_noalloc(
        &mut self,
        b: &Block,
        targeted_by_break: bool,
    ) -> hir::Block<'hir> {
        let (stmts, expr) = self.lower_stmts(&b.stmts);
        let rules = self.lower_block_check_mode(&b.rules);
        let hir_id = self.lower_node_id(b.id);
        hir::Block { hir_id, stmts, expr, rules, span: self.lower_span(b.span), targeted_by_break }
    }

    fn lower_stmts(
        &mut self,
        mut ast_stmts: &[Stmt],
    ) -> (&'hir [hir::Stmt<'hir>], Option<&'hir hir::Expr<'hir>>) {
        let mut stmts = SmallVec::<[hir::Stmt<'hir>; 8]>::new();
        let mut expr = None;
        while let [s, tail @ ..] = ast_stmts {
            match &s.kind {
                StmtKind::Local(local) => {
                    let hir_id = self.lower_node_id(s.id);
                    let local = self.lower_local(local);
                    self.alias_attrs(hir_id, local.hir_id);
                    let kind = hir::StmtKind::Local(local);
                    let span = self.lower_span(s.span);
                    stmts.push(hir::Stmt { hir_id, kind, span });
                }
                StmtKind::Item(it) => {
                    stmts.extend(self.lower_item_ref(it).into_iter().enumerate().map(
                        |(i, item_id)| {
                            let hir_id = match i {
                                0 => self.lower_node_id(s.id),
                                _ => self.next_id(),
                            };
                            let kind = hir::StmtKind::Item(item_id);
                            let span = self.lower_span(s.span);
                            hir::Stmt { hir_id, kind, span }
                        },
                    ));
                }
                StmtKind::Expr(e) => {
                    let e = self.lower_expr(e);
                    if tail.is_empty() {
                        expr = Some(e);
                    } else {
                        let hir_id = self.lower_node_id(s.id);
                        self.alias_attrs(hir_id, e.hir_id);
                        let kind = hir::StmtKind::Expr(e);
                        let span = self.lower_span(s.span);
                        stmts.push(hir::Stmt { hir_id, kind, span });
                    }
                }
                StmtKind::Semi(e) => {
                    let e = self.lower_expr(e);
                    let hir_id = self.lower_node_id(s.id);
                    self.alias_attrs(hir_id, e.hir_id);
                    let kind = hir::StmtKind::Semi(e);
                    let span = self.lower_span(s.span);
                    stmts.push(hir::Stmt { hir_id, kind, span });
                }
                StmtKind::Empty => {}
                StmtKind::MacCall(..) => panic!("shouldn't exist here"),
            }
            ast_stmts = &ast_stmts[1..];
        }
        (self.arena.alloc_from_iter(stmts), expr)
    }

    fn lower_local(&mut self, l: &Local) -> &'hir hir::Local<'hir> {
        let ty = l
            .ty
            .as_ref()
            .map(|t| self.lower_ty(t, &ImplTraitContext::Disallowed(ImplTraitPosition::Variable)));
        let init = l.kind.init().map(|init| self.lower_expr(init));
        let hir_id = self.lower_node_id(l.id);
        let pat = self.lower_pat(&l.pat);
        let els = if let LocalKind::InitElse(_, els) = &l.kind {
            Some(self.lower_block(els, false))
        } else {
            None
        };
        let span = self.lower_span(l.span);
        let source = hir::LocalSource::Normal;
        let attrs = self.lower_attrs(hir_id, &l.attrs);
        debug!("lower_local hir_id={hir_id:?} attrs={attrs:?}");
        let reuse_slot = attrs
            .map(|attrs| attrs.iter().any(|attr| attr.has_name(sym::rustc_reuse_upvar_slot)))
            .unwrap_or(false);
        let reuse_slot = if reuse_slot {
            if let Some(hir::Expr {
                kind: hir::ExprKind::Path(hir::QPath::Resolved(
                    None, hir::Path { res: hir::def::Res::Local(hir_id), .. })), .. }) = init
            {
                Some(*hir_id)
            } else {
                if init.is_some() {
                    panic!("init fed to let was not a simple upvar");
                } else {
                    panic!("with no init expression I cannot know what slot to use");
                }
            }
        } else {
            None
        };
        /*
        Some(Expr { hir_id: HirId { owner: OwnerId { def_id: DefId(0:5 ~ example_89213_c[f670]::wait) }, local_id: 8 },
                        kind: Path(Resolved(None, Path { span: example-89213-c.rs:9:53: 9:61 (#0), res: Local(HirId { owner: OwnerId { def_id: DefId(0:5 ~ example_89213_c[f670]::wait) }, local_id: 2 }), segments: [PathSegment { ident: an_upvar#0, hir_id: HirId { owner: OwnerId { def_id: DefId(0:5 ~ example_89213_c[f670]::wait) }, local_id: 7 }, res: Local(HirId { owner: OwnerId { def_id: DefId(0:5 ~ example_89213_c[f670]::wait) }, local_id: 2 }), args: None, infer_args: true }] })),
                        span: example-89213-c.rs:9:53: 9:61 (#0) })

         */
        debug!("lower_local reuse_slot={reuse_slot:?} init={init:?}");
        let local = self.arena.alloc(hir::Local { hir_id, ty, pat, init, els, reuse_slot, span, source });
        debug!(?local);
        local
    }

    fn lower_block_check_mode(&mut self, b: &BlockCheckMode) -> hir::BlockCheckMode {
        match *b {
            BlockCheckMode::Default => hir::BlockCheckMode::DefaultBlock,
            BlockCheckMode::Unsafe(u) => {
                hir::BlockCheckMode::UnsafeBlock(self.lower_unsafe_source(u))
            }
        }
    }
}
