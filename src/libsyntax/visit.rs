// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use abi::AbiSet;
use ast::*;
use ast;
use codemap::span;
use parse;
use opt_vec;
use opt_vec::OptVec;

// Context-passing AST walker. Each overridden visit method has full control
// over what happens with its node, it can do its own traversal of the node's
// children (potentially passing in different contexts to each), call
// visit::visit_* to apply the default traversal algorithm (again, it can
// override the context), or prevent deeper traversal by doing nothing.
//
// Note: it is an important invariant that the default visitor walks the body
// of a function in "execution order" (more concretely, reverse post-order
// with respect to the CFG implied by the AST), meaning that if AST node A may
// execute before AST node B, then A is visited first.  The borrow checker in
// particular relies on this property.

// Our typesystem doesn't do circular types, so the visitor record can not
// hold functions that take visitors. A vt enum is used to break the cycle.
#[deriving(Clone)]
pub enum vt<E> { mk_vt(visitor<E>), }

pub enum fn_kind<'self> {
    // fn foo() or extern "Abi" fn foo()
    fk_item_fn(ident, &'self Generics, purity, AbiSet),

    // fn foo(&self)
    fk_method(ident, &'self Generics, &'self method),

    // @fn(x, y) { ... }
    fk_anon(ast::Sigil),

    // |x, y| ...
    fk_fn_block,
}

pub fn name_of_fn(fk: &fn_kind) -> ident {
    match *fk {
      fk_item_fn(name, _, _, _) | fk_method(name, _, _) => {
          name
      }
      fk_anon(*) | fk_fn_block(*) => parse::token::special_idents::anon,
    }
}

pub fn generics_of_fn(fk: &fn_kind) -> Generics {
    match *fk {
        fk_item_fn(_, generics, _, _) |
        fk_method(_, generics, _) => {
            (*generics).clone()
        }
        fk_anon(*) | fk_fn_block(*) => {
            Generics {
                lifetimes: opt_vec::Empty,
                ty_params: opt_vec::Empty,
            }
        }
    }
}

#[cfg(stage0)]
pub trait Visitor {
    fn visit_mod(&self, m:&_mod, s:span, n:node_id);
    fn visit_view_item(&self, &view_item);
    fn visit_foreign_item(&self, @foreign_item);
    fn visit_item(&self, @item);
    fn visit_local(&self, @Local);
    fn visit_block(&self, &Block);
    fn visit_stmt(&self, @stmt);
    fn visit_arm(&self, &arm);
    fn visit_pat(&self, @pat);
    fn visit_decl(&self, @decl);
    fn visit_expr(&self, @expr);
    fn visit_expr_post(&self, @expr);
    fn visit_ty(&self, &Ty);
    fn visit_generics(&self, &Generics);
    fn visit_fn(&self, &fn_kind, &fn_decl, &Block, span, node_id);
    fn visit_ty_method(&self, &ty_method);
    fn visit_trait_method(&self, &trait_method);
    fn visit_struct_def(&self, @struct_def, ident, &Generics, node_id);
    fn visit_struct_field(&self, @struct_field);
}

#[cfg(not(stage0))]
pub trait Visitor {
    fn visit_mod(&self, m:&_mod, s:span, n:node_id) {
        self::walk_mod(self, m, s, n)
    }
    fn visit_view_item(&self, v:&view_item) {
        self::walk_view_item(self, v)
    }
    fn visit_foreign_item(&self, f:@foreign_item) {
        self::walk_foreign_item(self, f)
    }
    fn visit_item(&self, i:@item) {
        self::walk_item(self, i)
    }
    fn visit_local(&self, l:@local) {
        self::walk_local(self, l)
    }
    fn visit_block(&self, b:&blk) {
        self::walk_block(self, b)
    }
    fn visit_stmt(&self, s:@stmt) {
        self::walk_stmt(self, s)
    }
    fn visit_arm(&self, a:&arm) {
        self::walk_arm(self, a)
    }
    fn visit_pat(&self, p:@pat) {
        self::walk_pat(self, p)
    }
    fn visit_decl(&self, d:@decl) {
        self::walk_decl(self, d)
    }
    fn visit_expr(&self, e:@expr) {
        self::walk_expr(self, e)
    }

    // XXX default method (bug?) requires an arg even if unused.  and
    // underscore alone does not work there either, which seems
    // somehow worse
    fn visit_expr_post(&self, _e:@expr) { }

    fn visit_ty(&self, t:&Ty) {
        self::walk_ty(self, t)
    }
    fn visit_generics(&self, g:&Generics) {
        self::walk_generics(self, g)
    }
    fn visit_fn(&self, k:&fn_kind, d:&fn_decl, b:&blk, s:span, n:node_id) {
        self::walk_fn(self, k, d, b, s, n)
    }
    fn visit_ty_method(&self, t:&ty_method) {
        self::walk_ty_method(self, t)
    }
    fn visit_trait_method(&self, t: &trait_method) {
        self::walk_trait_method(self, t)
    }
    fn visit_struct_def(&self, d:@struct_def, i:ident, g:&Generics, n:node_id) {
        self::walk_struct_def(self, d, i, g, n)
    }
    fn visit_struct_field(&self, f:@struct_field) {
        self::walk_struct_field(self, f)
    }
}

pub struct ViaFns<E> {
    visit_mod: @fn(&_mod, span, node_id, (E, vt<E>)),
    visit_view_item: @fn(&view_item, (E, vt<E>)),
    visit_foreign_item: @fn(@foreign_item, (E, vt<E>)),
    visit_item: @fn(@item, (E, vt<E>)),
    visit_local: @fn(@Local, (E, vt<E>)),
    visit_block: @fn(&Block, (E, vt<E>)),
    visit_stmt: @fn(@stmt, (E, vt<E>)),
    visit_arm: @fn(&arm, (E, vt<E>)),
    visit_pat: @fn(@pat, (E, vt<E>)),
    visit_decl: @fn(@decl, (E, vt<E>)),
    visit_expr: @fn(@expr, (E, vt<E>)),
    visit_expr_post: @fn(@expr, (E, vt<E>)),
    visit_ty: @fn(&Ty, (E, vt<E>)),
    visit_generics: @fn(&Generics, (E, vt<E>)),
    visit_fn: @fn(&fn_kind, &fn_decl, &Block, span, node_id, (E, vt<E>)),
    visit_ty_method: @fn(&ty_method, (E, vt<E>)),
    visit_trait_method: @fn(&trait_method, (E, vt<E>)),
    visit_struct_def: @fn(@struct_def, ident, &Generics, node_id, (E, vt<E>)),
    visit_struct_field: @fn(@struct_field, (E, vt<E>)),
}

pub type visitor<E> = @ViaFns<E>;

fn visit_fns<E>(e_vt:&(E, vt<E>)) -> visitor<E> {
    let &(_, mk_vt(f)) = e_vt; f
}

impl<E:Clone> Visitor for (E, vt<E>) {
    fn visit_mod(&self, m:&_mod, s:span, n:node_id) {
        (visit_fns(self).visit_mod)(m, s, n, self.clone())
    }
    fn visit_view_item(&self, v:&view_item) {
        (visit_fns(self).visit_view_item)(v, self.clone())
    }
    fn visit_foreign_item(&self, i:@foreign_item) {
        (visit_fns(self).visit_foreign_item)(i, self.clone())
    }
    fn visit_item(&self, i:@item) {
        (visit_fns(self).visit_item)(i, self.clone())
    }
    fn visit_local(&self, l:@Local) {
        (visit_fns(self).visit_local)(l, self.clone())
    }
    fn visit_block(&self, b:&Block) {
        (visit_fns(self).visit_block)(b, self.clone())
    }
    fn visit_stmt(&self, s:@stmt) {
        (visit_fns(self).visit_stmt)(s, self.clone())
    }
    fn visit_arm(&self, a:&arm) {
        (visit_fns(self).visit_arm)(a, self.clone())
    }
    fn visit_pat(&self, p:@pat) {
        (visit_fns(self).visit_pat)(p, self.clone())
    }
    fn visit_decl(&self, d:@decl) {
        (visit_fns(self).visit_decl)(d, self.clone())
    }
    fn visit_expr(&self, e:@expr) {
        (visit_fns(self).visit_expr)(e, self.clone())
    }
    fn visit_expr_post(&self, e:@expr) {
        (visit_fns(self).visit_expr_post)(e, self.clone())
    }
    fn visit_ty(&self, t:&Ty) {
        (visit_fns(self).visit_ty)(t, self.clone())
    }
    fn visit_generics(&self, g:&Generics) {
        (visit_fns(self).visit_generics)(g, self.clone())
    }
    fn visit_fn(&self, k:&fn_kind, d:&fn_decl, b:&Block, s:span, n:node_id) {
        (visit_fns(self).visit_fn)(k, d, b, s, n, self.clone())
    }
    fn visit_ty_method(&self, m:&ty_method) {
        (visit_fns(self).visit_ty_method)(m, self.clone())
    }
    fn visit_trait_method(&self, t:&trait_method) {
        (visit_fns(self).visit_trait_method)(t, self.clone())
    }
    fn visit_struct_def(&self, d:@struct_def, i:ident, g:&Generics, n:node_id) {
        (visit_fns(self).visit_struct_def)(d, i, g, n, self.clone())
    }
    fn visit_struct_field(&self, s:@struct_field) {
        (visit_fns(self).visit_struct_field)(s, self.clone())
    }
}

pub fn default_visitor<E:Clone>() -> visitor<E> {
    return @ViaFns {
        visit_mod: |a,b,c,d|self::visit_mod::<E>(a, b, c, d),
        visit_view_item: |a,b|self::visit_view_item::<E>(a, b),
        visit_foreign_item: |a,b|self::visit_foreign_item::<E>(a, b),
        visit_item: |a,b|self::visit_item::<E>(a, b),
        visit_local: |a,b|self::visit_local::<E>(a, b),
        visit_block: |a,b|self::visit_block::<E>(a, b),
        visit_stmt: |a,b|self::visit_stmt::<E>(a, b),
        visit_arm: |a,b|self::visit_arm::<E>(a, b),
        visit_pat: |a,b|self::visit_pat::<E>(a, b),
        visit_decl: |a,b|self::visit_decl::<E>(a, b),
        visit_expr: |a,b|self::visit_expr::<E>(a, b),
        visit_expr_post: |_a,_b| (),
        visit_ty: |a,b|self::skip_ty::<E>(a, b),
        visit_generics: |a,b|self::visit_generics::<E>(a, b),
        visit_fn: |a,b,c,d,e,f|self::visit_fn::<E>(a, b, c, d, e, f),
        visit_ty_method: |a,b|self::visit_ty_method::<E>(a, b),
        visit_trait_method: |a,b|self::visit_trait_method::<E>(a, b),
        visit_struct_def: |a,b,c,d,e|self::visit_struct_def::<E>(a, b, c, d, e),
        visit_struct_field: |a,b|self::visit_struct_field::<E>(a, b),
    };
}

pub fn visit_crate<E:Clone>(c: &Crate, e_vt: (E, vt<E>)) {
    e_vt.visit_mod(&c.module, c.span, crate_node_id);
}

pub fn visit_mod<E:Clone>(m: &_mod, sp: span, id: node_id, e_vt: (E, vt<E>)) {
    walk_mod(&e_vt, m, sp, id)
}

pub fn walk_mod<V:Visitor>(v:&V, m: &_mod, _: span, _: node_id) {
    for m.view_items.iter().advance |vi| {
        v.visit_view_item(vi);
    }
    for m.items.iter().advance |i| {
        v.visit_item(*i);
    }
}

pub fn visit_view_item<E:Clone>(vi: &view_item, e_vt: (E, vt<E>)) {
    walk_view_item(&e_vt, vi)
}

pub fn walk_view_item<V:Visitor>(_v:&V, _vi: &view_item) { }

pub fn visit_local<E:Clone>(loc: &local, e_vt: (E, vt<E>)) {
    walk_local(&e_vt, loc)
}

pub fn walk_local<V:Visitor>(v:&V, loc: &Local) {
    v.visit_pat(loc.pat);
    v.visit_ty(&loc.ty);
    match loc.init {
      None => (),
      Some(ex) => v.visit_expr(ex)
    }
}

fn visit_trait_ref<E:Clone>(tref: &ast::trait_ref, e_vt: (E, vt<E>)) {
    walk_trait_ref(&e_vt, tref);
}

fn walk_trait_ref<V:Visitor>(v:&V, tref: &ast::trait_ref) {
    walk_path(v, &tref.path);
}

pub fn visit_item<E:Clone>(i: &item, e_vt: (E, vt<E>)) {
    walk_item(&e_vt, i);
}

pub fn walk_item<V:Visitor>(v:&V, i: &item) {
    match i.node {
        item_static(ref t, _, ex) => {
            v.visit_ty(t);
            v.visit_expr(ex);
        }
        item_fn(ref decl, purity, abi, ref generics, ref body) => {
            v.visit_fn(
                &fk_item_fn(
                    i.ident,
                    generics,
                    purity,
                    abi
                ),
                decl,
                body,
                i.span,
                i.id
            );
        }
        item_mod(ref m) => v.visit_mod(m, i.span, i.id),
        item_foreign_mod(ref nm) => {
            for nm.view_items.iter().advance |vi| {
                v.visit_view_item(vi);
            }
            for nm.items.iter().advance |ni| {
                v.visit_foreign_item(*ni);
            }
        }
        item_ty(ref t, ref tps) => {
            v.visit_ty(t);
            v.visit_generics(tps);
        }
        item_enum(ref enum_definition, ref tps) => {
            v.visit_generics(tps);
            walk_enum_def(
                v,
                enum_definition,
                tps
            );
        }
        item_impl(ref tps, ref traits, ref ty, ref methods) => {
            v.visit_generics(tps);
            for traits.iter().advance |p| {
                walk_trait_ref(v, p);
            }
            v.visit_ty(ty);
            for methods.iter().advance |m| {
                walk_method_helper(v, *m)
            }
        }
        item_struct(struct_def, ref generics) => {
            v.visit_generics(generics);
            v.visit_struct_def(struct_def, i.ident, generics, i.id);
        }
        item_trait(ref generics, ref traits, ref methods) => {
            v.visit_generics(generics);
            for traits.iter().advance |p| {
                walk_path(v, &p.path);
            }
            for methods.iter().advance |m| {
                v.visit_trait_method(m);
            }
        }
        item_mac(ref m) => walk_mac(v, m)
    }
}

pub fn visit_enum_def<E:Clone>(enum_definition: &ast::enum_def,
                               tps: &Generics,
                               e_vt: (E, vt<E>)) {
    walk_enum_def(&e_vt, enum_definition, tps)
}

pub fn walk_enum_def<V:Visitor>(v:&V,
                                enum_definition: &ast::enum_def,
                                tps: &Generics) {
    for enum_definition.variants.iter().advance |vr| {
        match vr.node.kind {
            tuple_variant_kind(ref variant_args) => {
                for variant_args.iter().advance |va| {
                    v.visit_ty(&va.ty);
                }
            }
            struct_variant_kind(struct_def) => {
                v.visit_struct_def(struct_def, vr.node.name, tps, vr.node.id);
            }
        }
        // Visit the disr expr if it exists
        for vr.node.disr_expr.iter().advance |ex| {
            v.visit_expr(*ex)
        }
    }
}

pub fn skip_ty<E>(_t: &Ty, (_e,_v): (E, vt<E>)) {}

pub fn visit_ty<E:Clone>(t: &Ty, e_vt: (E, vt<E>)) {
    walk_ty(&e_vt, t)
}

pub fn walk_ty<V:Visitor>(v:&V, t: &Ty) {
    match t.node {
        ty_box(ref mt) | ty_uniq(ref mt) |
        ty_vec(ref mt) | ty_ptr(ref mt) | ty_rptr(_, ref mt) => {
            v.visit_ty(mt.ty);
        },
        ty_tup(ref ts) => {
            for ts.iter().advance |tt| {
                v.visit_ty(tt);
            }
        },
        ty_closure(ref f) => {
            for f.decl.inputs.iter().advance |a| {
                v.visit_ty(&a.ty);
            }
            v.visit_ty(&f.decl.output);
            do f.bounds.map |bounds| {
                walk_ty_param_bounds(v, bounds);
            };
        },
        ty_bare_fn(ref f) => {
            for f.decl.inputs.iter().advance |a| {
                v.visit_ty(&a.ty);
            }
            v.visit_ty(&f.decl.output);
        },
        ty_path(ref p, ref bounds, _) => {
            walk_path(v, p);
            do bounds.map |bounds| {
                walk_ty_param_bounds(v, bounds);
            };
        },
        ty_fixed_length_vec(ref mt, ex) => {
            v.visit_ty(mt.ty);
            v.visit_expr(ex);
        },
        ty_nil | ty_bot | ty_mac(_) | ty_infer => ()
    }
}

pub fn visit_path<E:Clone>(p: &Path, e_vt: (E, vt<E>)) {
    walk_path(&e_vt, p)
}

pub fn walk_path<V:Visitor>(v:&V, p: &Path) {
    for p.types.iter().advance |tp| { v.visit_ty(tp); }
}

pub fn visit_pat<E:Clone>(p: &pat, e_vt: (E, vt<E>)) {
    walk_pat(&e_vt, p)
}

pub fn walk_pat<V:Visitor>(v:&V, p: &pat) {
    match p.node {
        pat_enum(ref path, ref children) => {
            walk_path(v, path);
            for children.iter().advance |children| {
                for children.iter().advance |child| {
                    v.visit_pat(*child);
                }
            }
        }
        pat_struct(ref path, ref fields, _) => {
            walk_path(v, path);
            for fields.iter().advance |f| {
                v.visit_pat(f.pat);
            }
        }
        pat_tup(ref elts) => {
            for elts.iter().advance |elt| {
                v.visit_pat(*elt);
            }
        },
        pat_box(inner) | pat_uniq(inner) | pat_region(inner) => {
            v.visit_pat(inner)
        },
        pat_ident(_, ref path, ref inner) => {
            walk_path(v, path);
            for inner.iter().advance |subpat| {
                v.visit_pat(*subpat)
            }
        }
        pat_lit(ex) => v.visit_expr(ex),
        pat_range(e1, e2) => {
            v.visit_expr(e1);
            v.visit_expr(e2);
        }
        pat_wild => (),
        pat_vec(ref before, ref slice, ref after) => {
            for before.iter().advance |elt| {
                v.visit_pat(*elt);
            }
            for slice.iter().advance |elt| {
                v.visit_pat(*elt);
            }
            for after.iter().advance |tail| {
                v.visit_pat(*tail);
            }
        }
    }
}

pub fn visit_foreign_item<E:Clone>(ni: &foreign_item, e_vt: (E, vt<E>)) {
    walk_foreign_item(&e_vt, ni)
}

pub fn walk_foreign_item<V:Visitor>(v:&V, ni: &foreign_item) {
    match ni.node {
        foreign_item_fn(ref fd, _, ref generics) => {
            walk_fn_decl(v, fd);
            v.visit_generics(generics);
        }
        foreign_item_static(ref t, _) => {
            v.visit_ty(t);
        }
    }
}

pub fn visit_ty_param_bounds<E:Clone>(bounds: &OptVec<TyParamBound>,
                                      e_vt: (E, vt<E>)) {
    walk_ty_param_bounds(&e_vt, bounds);
}

pub fn walk_ty_param_bounds<V:Visitor>(v:&V, bounds: &OptVec<TyParamBound>) {
    for bounds.iter().advance |bound| {
        match *bound {
            TraitTyParamBound(ref ty) => walk_trait_ref(v, ty),
            RegionTyParamBound => {}
        }
    }
}

pub fn visit_generics<E:Clone>(generics: &Generics, e_vt: (E, vt<E>)) {
    walk_generics(&e_vt, generics)
}

pub fn walk_generics<V:Visitor>(v:&V, generics: &Generics) {
    for generics.ty_params.iter().advance |tp| {
        walk_ty_param_bounds(v, &tp.bounds);
    }
}

pub fn visit_fn_decl<E:Clone>(fd: &fn_decl, e_vt: (E, vt<E>)) {
    walk_fn_decl(&e_vt, fd)
}

pub fn walk_fn_decl<V:Visitor>(v:&V, fd: &fn_decl) {
    for fd.inputs.iter().advance |a| {
        v.visit_pat(a.pat);
        v.visit_ty(&a.ty);
    }
    v.visit_ty(&fd.output);
}

// Note: there is no visit_method() method in the visitor, instead override
// visit_fn() and check for fk_method().  I named this visit_method_helper()
// because it is not a default impl of any method, though I doubt that really
// clarifies anything. - Niko
pub fn visit_method_helper<E:Clone>(m: &method, e_vt: (E, vt<E>)) {
    walk_method_helper(&e_vt, m)
}

pub fn walk_method_helper<V:Visitor>(v:&V, m: &method) {
    v.visit_fn(&fk_method(m.ident, &m.generics, m),
               &m.decl,
               &m.body,
               m.span,
               m.id);
}

pub fn visit_fn<E:Clone>(fk: &fn_kind, decl: &fn_decl, body: &Block, sp: span,
                         id: node_id, e_vt: (E, vt<E>)) {
    walk_fn(&e_vt, fk, decl, body, sp, id)
}

pub fn walk_fn<V:Visitor>(v:&V, fk: &fn_kind, decl: &fn_decl, body: &Block,
                          _sp: span, _id: node_id) {
    walk_fn_decl(v, decl);
    let generics = generics_of_fn(fk);
    v.visit_generics(&generics);
    v.visit_block(body);
}

pub fn visit_ty_method<E:Clone>(m: &ty_method, e_vt: (E, vt<E>)) {
    walk_ty_method(&e_vt, m)
}

pub fn walk_ty_method<V:Visitor>(v:&V, m: &ty_method) {
    for m.decl.inputs.iter().advance |a| {
        v.visit_ty(&a.ty);
    }
    v.visit_generics(&m.generics);
    v.visit_ty(&m.decl.output);
}

pub fn visit_trait_method<E:Clone>(m: &trait_method, e_vt: (E, vt<E>)) {
    walk_trait_method(&e_vt, m)
}

pub fn walk_trait_method<V:Visitor>(v:&V, m: &trait_method) {
    match *m {
        required(ref ty_m) => v.visit_ty_method(ty_m),
        provided(m) => walk_method_helper(v, m)
    }
}

pub fn visit_struct_def<E:Clone>(sd: @struct_def, nm: ast::ident,
                                 g: &Generics, id: node_id, e_vt: (E, vt<E>)) {
    walk_struct_def(&e_vt, sd, nm, g, id)
}

pub fn walk_struct_def<V:Visitor>(v:&V, sd: @struct_def,
                                  _nm: ast::ident, _: &Generics, _: node_id) {
    for sd.fields.iter().advance |f| {
        v.visit_struct_field(*f);
    }
}

pub fn visit_struct_field<E:Clone>(sf: &struct_field, e_vt: (E, vt<E>)) {
    walk_struct_field(&e_vt, sf);
}

pub fn walk_struct_field<V:Visitor>(v:&V, sf: &struct_field) {
    v.visit_ty(&sf.node.ty);
}

pub fn visit_block<E:Clone>(b: &Block, e_vt: (E, vt<E>)) {
    walk_block(&e_vt, b)
}

pub fn walk_block<V:Visitor>(v:&V, b: &Block) {
    for b.view_items.iter().advance |vi| {
        v.visit_view_item(vi);
    }
    for b.stmts.iter().advance |s| {
        v.visit_stmt(*s);
    }
    walk_expr_opt(v, b.expr);
}

pub fn visit_stmt<E:Clone>(s: &stmt, e_vt: (E, vt<E>)) {
    walk_stmt(&e_vt, s)
}

pub fn walk_stmt<V:Visitor>(v:&V, s: &stmt) {
    match s.node {
        stmt_decl(d, _) => v.visit_decl(d),
        stmt_expr(ex, _) => v.visit_expr(ex),
        stmt_semi(ex, _) => v.visit_expr(ex),
        stmt_mac(ref mac, _) => walk_mac(v, mac)
    }
}

pub fn visit_decl<E:Clone>(d: &decl, e_vt: (E, vt<E>)) {
    walk_decl(&e_vt, d)
}

pub fn walk_decl<V:Visitor>(v:&V, d: &decl) {
    match d.node {
        decl_local(ref loc) => v.visit_local(*loc),
        decl_item(it) => v.visit_item(it)
    }
}

pub fn visit_expr_opt<E:Clone>(eo: Option<@expr>, e_vt: (E, vt<E>)) {
    walk_expr_opt(&e_vt, eo)
}

pub fn walk_expr_opt<V:Visitor>(v:&V, eo: Option<@expr>) {
    match eo { None => (), Some(ex) => v.visit_expr(ex) }
}

pub fn visit_exprs<E:Clone>(exprs: &[@expr], e_vt: (E, vt<E>)) {
    walk_exprs(&e_vt, exprs)
}

pub fn walk_exprs<V:Visitor>(v:&V, exprs: &[@expr]) {
    for exprs.iter().advance |ex| { v.visit_expr(*ex); }
}

pub fn visit_mac<E:Clone>(m: &mac, e_vt: (E, vt<E>)) {
    walk_mac(&e_vt, m)
}

pub fn walk_mac<V:Visitor>(_v:&V, _m: &mac) {
    /* no user-serviceable parts inside */
}

pub fn visit_expr<E:Clone>(ex: @expr, e_vt: (E, vt<E>)) {
    walk_expr(&e_vt, ex)
}

pub fn walk_expr<V:Visitor>(v:&V, ex: @expr) {
    match ex.node {
        expr_vstore(x, _) => v.visit_expr(x),
        expr_vec(ref es, _) => walk_exprs(v, *es),
        expr_repeat(element, count, _) => {
            v.visit_expr(element);
            v.visit_expr(count);
        }
        expr_struct(ref p, ref flds, base) => {
            walk_path(v, p);
            for flds.iter().advance |f| {
<<<<<<< HEAD
                (v.visit_expr)(f.expr, (e.clone(), v));
||||||| merged common ancestors
                (v.visit_expr)(f.node.expr, (e.clone(), v));
=======
                v.visit_expr(f.node.expr);
>>>>>>> checkpoint
            }
            walk_expr_opt(v, base);
        }
        expr_tup(ref elts) => {
            for elts.iter().advance |el| { v.visit_expr(*el) }
        }
        expr_call(callee, ref args, _) => {
            walk_exprs(v, *args);
            v.visit_expr(callee);
        }
        expr_method_call(_, callee, _, ref tys, ref args, _) => {
            walk_exprs(v, *args);
            for tys.iter().advance |tp| {
                v.visit_ty(tp);
            }
            v.visit_expr(callee);
        }
        expr_binary(_, _, a, b) => {
            v.visit_expr(a);
            v.visit_expr(b);
        }
        expr_addr_of(_, x) | expr_unary(_, _, x) |
        expr_loop_body(x) | expr_do_body(x) => v.visit_expr(x),
        expr_lit(_) => (),
        expr_cast(x, ref t) => {
            v.visit_expr(x);
            v.visit_ty(t);
        }
        expr_if(x, ref b, eo) => {
            v.visit_expr(x);
            v.visit_block(b);
            walk_expr_opt(v, eo);
        }
        expr_while(x, ref b) => {
            v.visit_expr(x);
            v.visit_block(b);
        }
        expr_loop(ref b, _) => v.visit_block(b),
        expr_match(x, ref arms) => {
            v.visit_expr(x);
            for arms.iter().advance |a| { v.visit_arm(a); }
        }
        expr_fn_block(ref decl, ref body) => {
            v.visit_fn(
                &fk_fn_block,
                decl,
                body,
                ex.span,
                ex.id
            );
        }
        expr_block(ref b) => v.visit_block(b),
        expr_assign(a, b) => {
            v.visit_expr(b);
            v.visit_expr(a);
        }
        expr_assign_op(_, _, a, b) => {
            v.visit_expr(b);
            v.visit_expr(a);
        }
        expr_field(x, _, ref tys) => {
            v.visit_expr(x);
            for tys.iter().advance |tp| {
                v.visit_ty(tp);
            }
        }
        expr_index(_, a, b) => {
            v.visit_expr(a);
            v.visit_expr(b);
        }
        expr_path(ref p) => walk_path(v, p),
        expr_self => (),
        expr_break(_) => (),
        expr_again(_) => (),
        expr_ret(eo) => walk_expr_opt(v, eo),
        expr_log(lv, x) => {
            v.visit_expr(lv);
            v.visit_expr(x);
        }
        expr_mac(ref mac) => walk_mac(v, mac),
        expr_paren(x) => v.visit_expr(x),
        expr_inline_asm(ref a) => {
            for a.inputs.iter().advance |&(_, in)| {
                v.visit_expr(in);
            }
            for a.outputs.iter().advance |&(_, out)| {
                v.visit_expr(out);
            }
        }
    }
    v.visit_expr_post(ex);
}

pub fn visit_arm<E:Clone>(a: &arm, e_vt: (E, vt<E>)) {
    walk_arm(&e_vt, a)
}

pub fn walk_arm<V:Visitor>(v:&V, a: &arm) {
    for a.pats.iter().advance |p| { v.visit_pat(*p); }
    walk_expr_opt(v, a.guard);
    v.visit_block(&a.body);
}

// Simpler, non-context passing interface. Always walks the whole tree, simply
// calls the given functions on the nodes.

pub struct SimpleVisitor {
    visit_mod: @fn(&_mod, span, node_id),
    visit_view_item: @fn(&view_item),
    visit_foreign_item: @fn(@foreign_item),
    visit_item: @fn(@item),
    visit_local: @fn(@Local),
    visit_block: @fn(&Block),
    visit_stmt: @fn(@stmt),
    visit_arm: @fn(&arm),
    visit_pat: @fn(@pat),
    visit_decl: @fn(@decl),
    visit_expr: @fn(@expr),
    visit_expr_post: @fn(@expr),
    visit_ty: @fn(&Ty),
    visit_generics: @fn(&Generics),
    visit_fn: @fn(&fn_kind, &fn_decl, &Block, span, node_id),
    visit_ty_method: @fn(&ty_method),
    visit_trait_method: @fn(&trait_method),
    visit_struct_def: @fn(@struct_def, ident, &Generics, node_id),
    visit_struct_field: @fn(@struct_field),
    visit_struct_method: @fn(@method)
}

pub type simple_visitor = @SimpleVisitor;

pub fn simple_ignore_ty(_t: &Ty) {}

pub fn default_simple_visitor() -> @SimpleVisitor {
    @SimpleVisitor {
        visit_mod: |_m, _sp, _id| { },
        visit_view_item: |_vi| { },
        visit_foreign_item: |_ni| { },
        visit_item: |_i| { },
        visit_local: |_l| { },
        visit_block: |_b| { },
        visit_stmt: |_s| { },
        visit_arm: |_a| { },
        visit_pat: |_p| { },
        visit_decl: |_d| { },
        visit_expr: |_e| { },
        visit_expr_post: |_e| { },
        visit_ty: simple_ignore_ty,
        visit_generics: |_| {},
        visit_fn: |_, _, _, _, _| {},
        visit_ty_method: |_| {},
        visit_trait_method: |_| {},
        visit_struct_def: |_, _, _, _| {},
        visit_struct_field: |_| {},
        visit_struct_method: |_| {},
    }
}

pub fn mk_simple_visitor(v: simple_visitor) -> vt<()> {
    fn v_mod(
        f: @fn(&_mod, span, node_id),
        m: &_mod,
        sp: span,
        id: node_id,
        e_vt: ((), vt<()>)
    ) {
        f(m, sp, id);
        visit_mod(m, sp, id, e_vt);
    }
    fn v_view_item(f: @fn(&view_item), vi: &view_item, e_vt: ((), vt<()>)) {
        f(vi);
        visit_view_item(vi, e_vt);
    }
    fn v_foreign_item(f: @fn(@foreign_item), ni: @foreign_item, e_vt: ((), vt<()>)) {
        f(ni);
        visit_foreign_item(ni, e_vt);
    }
    fn v_item(f: @fn(@item), i: @item, e_vt: ((), vt<()>)) {
        f(i);
        visit_item(i, e_vt);
    }
    fn v_local(f: @fn(@Local), l: @Local, e_vt: ((), vt<()>)) {
        f(l);
        visit_local(l, e_vt);
    }
    fn v_block(f: @fn(&ast::Block), bl: &ast::Block, e_vt: ((), vt<()>)) {
        f(bl);
        visit_block(bl, e_vt);
    }
    fn v_stmt(f: @fn(@stmt), st: @stmt, e_vt: ((), vt<()>)) {
        f(st);
        visit_stmt(st, e_vt);
    }
    fn v_arm(f: @fn(&arm), a: &arm, e_vt: ((), vt<()>)) {
        f(a);
        visit_arm(a, e_vt);
    }
    fn v_pat(f: @fn(@pat), p: @pat, e_vt: ((), vt<()>)) {
        f(p);
        visit_pat(p, e_vt);
    }
    fn v_decl(f: @fn(@decl), d: @decl, e_vt: ((), vt<()>)) {
        f(d);
        visit_decl(d, e_vt);
    }
    fn v_expr(f: @fn(@expr), ex: @expr, e_vt: ((), vt<()>)) {
        f(ex);
        visit_expr(ex, e_vt);
    }
    fn v_expr_post(f: @fn(@expr), ex: @expr, (_e, _v): ((), vt<()>)) {
        f(ex);
    }
    fn v_ty(f: @fn(&Ty), ty: &Ty, e_vt: ((), vt<()>)) {
        f(ty);
        visit_ty(ty, e_vt);
    }
    fn v_ty_method(f: @fn(&ty_method), ty: &ty_method, e_vt: ((), vt<()>)) {
        f(ty);
        visit_ty_method(ty, e_vt);
    }
    fn v_trait_method(f: @fn(&trait_method),
                      m: &trait_method,
                      e_vt: ((), vt<()>)) {
        f(m);
        visit_trait_method(m, e_vt);
    }
    fn v_struct_def(
        f: @fn(@struct_def, ident, &Generics, node_id),
        sd: @struct_def,
        nm: ident,
        generics: &Generics,
        id: node_id,
        e_vt: ((), vt<()>)
    ) {
        f(sd, nm, generics, id);
        visit_struct_def(sd, nm, generics, id, e_vt);
    }
    fn v_generics(
        f: @fn(&Generics),
        ps: &Generics,
        e_vt: ((), vt<()>)
    ) {
        f(ps);
        visit_generics(ps, e_vt);
    }
    fn v_fn(
        f: @fn(&fn_kind, &fn_decl, &Block, span, node_id),
        fk: &fn_kind,
        decl: &fn_decl,
        body: &Block,
        sp: span,
        id: node_id,
        e_vt: ((), vt<()>)
    ) {
        f(fk, decl, body, sp, id);
        visit_fn(fk, decl, body, sp, id, e_vt);
    }
    let visit_ty: @fn(&Ty, ((), vt<()>)) =
        |a,b| v_ty(v.visit_ty, a, b);
    fn v_struct_field(f: @fn(@struct_field), sf: @struct_field, e_vt: ((), vt<()>)) {
        f(sf);
        visit_struct_field(sf, e_vt);
    }
    return mk_vt(@ViaFns {
        visit_mod: |a,b,c,d|v_mod(v.visit_mod, a, b, c, d),
        visit_view_item: |a,b| v_view_item(v.visit_view_item, a, b),
        visit_foreign_item:
            |a,b|v_foreign_item(v.visit_foreign_item, a, b),
        visit_item: |a,b|v_item(v.visit_item, a, b),
        visit_local: |a,b|v_local(v.visit_local, a, b),
        visit_block: |a,b|v_block(v.visit_block, a, b),
        visit_stmt: |a,b|v_stmt(v.visit_stmt, a, b),
        visit_arm: |a,b|v_arm(v.visit_arm, a, b),
        visit_pat: |a,b|v_pat(v.visit_pat, a, b),
        visit_decl: |a,b|v_decl(v.visit_decl, a, b),
        visit_expr: |a,b|v_expr(v.visit_expr, a, b),
        visit_expr_post: |a,b| v_expr_post(v.visit_expr_post, a, b),
        visit_ty: visit_ty,
        visit_generics: |a,b|
            v_generics(v.visit_generics, a, b),
        visit_fn: |a,b,c,d,e,f|
            v_fn(v.visit_fn, a, b, c, d, e, f),
        visit_ty_method: |a,b|
            v_ty_method(v.visit_ty_method, a, b),
        visit_trait_method: |a,b|
            v_trait_method(v.visit_trait_method, a, b),
        visit_struct_def: |a,b,c,d,e|
            v_struct_def(v.visit_struct_def, a, b, c, d, e),
        visit_struct_field: |a,b|
            v_struct_field(v.visit_struct_field, a, b),
    });
}
