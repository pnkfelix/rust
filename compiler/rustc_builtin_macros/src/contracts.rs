#![allow(unused_imports, unused_variables)] // XXX

use rustc_ast::ptr::P;
use rustc_ast::{self as ast, AttrVec, Expr, FnHeader, FnSig, Generics, Param, StmtKind};
use rustc_ast::{Fn, ItemKind, Mutability, Safety, Stmt, Ty, TyKind};
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::symbol::{kw, sym, Ident, Symbol};
use rustc_span::Span;
use thin_vec::{thin_vec, ThinVec};

pub(crate) fn expand_requires(
    ecx: &mut ExtCtxt<'_>,
    _span: Span,
    meta_item: &ast::MetaItem,
    item: Annotatable,
) -> Vec<Annotatable> {
    vec![item]
}

pub(crate) fn expand_ensures(
    ecx: &mut ExtCtxt<'_>,
    _span: Span,
    meta_item: &ast::MetaItem,
    item: Annotatable,
) -> Vec<Annotatable> {
    vec![item]
}
