// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::prelude::*;

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
pub enum vt<E> { mk_vt(visitor<E>), }

pub enum fn_kind<'self> {
    // fn foo() or extern "Abi" fn foo()
    fk_item_fn(ident, &'self Generics, purity, AbiSet),

    // fn foo(&self)
    fk_method(ident, &'self Generics, &'self method),

    // fn@(x, y) { ... }
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
            copy *generics
        }
        fk_anon(*) | fk_fn_block(*) => {
            Generics {
                lifetimes: opt_vec::Empty,
                ty_params: opt_vec::Empty,
            }
        }
    }
}

trait Visitor {
    #[cfg(not(stage2))]
    fn visit_mod(&self, m:&_mod, s:span, i:node_id);
    #[cfg(stage2)]
    fn visit_mod(&self, m:&_mod, s:span, i:node_id) {
        walk_mod(self, m, s, i);
    }
    fn visit_view_item(&self, @view_item);
    fn visit_foreign_item(&self, @foreign_item);
    fn visit_item(&self, @item);
    fn visit_local(&self, @local);
    fn visit_block(&self, &blk);
    fn visit_stmt(&self, @stmt);
    fn visit_arm(&self, &arm);
    fn visit_pat(&self, @pat);
    fn visit_decl(&self, @decl);
    fn visit_expr(&self, @expr);
    fn visit_expr_post(&self, @expr);
    fn visit_ty(&self, @Ty);
    fn visit_generics(&self, &Generics);
    fn visit_fn(&self, &fn_kind, &fn_decl, &blk, span, node_id);
    fn visit_ty_method(&self, &ty_method);
    fn visit_trait_method(&self, &trait_method);
    fn visit_struct_def(&self, @struct_def, ident, &Generics, node_id);
    fn visit_struct_field(&self, @struct_field);
    fn visit_struct_method(&self, @method);
}

pub struct VisitorStruct<E> {
    visit_mod: @fn(&_mod, span, node_id, (E, vt<E>)),
    visit_view_item: @fn(@view_item, (E, vt<E>)),
    visit_foreign_item: @fn(@foreign_item, (E, vt<E>)),
    visit_item: @fn(@item, (E, vt<E>)),
    visit_local: @fn(@local, (E, vt<E>)),
    visit_block: @fn(&blk, (E, vt<E>)),
    visit_stmt: @fn(@stmt, (E, vt<E>)),
    visit_arm: @fn(&arm, (E, vt<E>)),
    visit_pat: @fn(@pat, (E, vt<E>)),
    visit_decl: @fn(@decl, (E, vt<E>)),
    visit_expr: @fn(@expr, (E, vt<E>)),
    visit_expr_post: @fn(@expr, (E, vt<E>)),
    visit_ty: @fn(@Ty, (E, vt<E>)),
    visit_generics: @fn(&Generics, (E, vt<E>)),
    visit_fn: @fn(&fn_kind, &fn_decl, &blk, span, node_id, (E, vt<E>)),
    visit_ty_method: @fn(&ty_method, (E, vt<E>)),
    visit_trait_method: @fn(&trait_method, (E, vt<E>)),
    visit_struct_def: @fn(@struct_def, ident, &Generics, node_id, (E, vt<E>)),
    visit_struct_field: @fn(@struct_field, (E, vt<E>)),
    visit_struct_method: @fn(@method, (E, vt<E>))
}

impl<E:Copy> Visitor for (E, vt<E>) {
    fn visit_mod(&self, m: &_mod, s: span, i: node_id) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_mod)(m, s, i, copy *self);
    }
    fn visit_view_item(&self, i: @view_item) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_view_item)(i, copy *self);
    }
    fn visit_foreign_item(&self, i: @foreign_item) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_foreign_item)(i, copy *self);
    }
    fn visit_item(&self, i: @item) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_item)(i, copy *self);
    }
    fn visit_local(&self, l: @local) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_local)(l, copy *self);
    }
    fn visit_block(&self, b: &blk) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_block)(b, copy *self);
    }
    fn visit_stmt(&self, s: @stmt) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_stmt)(s, copy *self);
    }
    fn visit_arm(&self, a: &arm) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_arm)(a, copy *self);
    }
    fn visit_pat(&self, p: @pat) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_pat)(p, copy *self);
    }
    fn visit_decl(&self, d: @decl) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_decl)(d, copy *self);
    }
    fn visit_expr(&self, e: @expr) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_expr)(e, copy *self);
    }
    fn visit_expr_post(&self, e: @expr) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_expr_post)(e, copy *self);
    }
    fn visit_ty(&self, t: @Ty) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_ty)(t, copy *self);
    }
    fn visit_generics(&self, g: &Generics) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_generics)(g, copy *self);
    }
    fn visit_fn(&self, k: &fn_kind, d: &fn_decl, b: &blk, s: span, n: node_id) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_fn)(k, d, b, s, n, copy *self);
    }
    fn visit_ty_method(&self, m: &ty_method) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_ty_method)(m, copy *self);
    }
    fn visit_trait_method(&self, m: &trait_method) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_trait_method)(m, copy *self);
    }
    fn visit_struct_def(&self, d: @struct_def, i: ident, g: &Generics, n: node_id) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_struct_def)(d, i, g, n, copy *self);
    }
    fn visit_struct_field(&self, f: @struct_field) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_struct_field)(f, copy *self);
    }
    fn visit_struct_method(&self, m: @method) {
        let &(_, mk_vt(ref v)) = self;
        (v.visit_struct_method)(m, copy *self);
    }
}

pub type visitor<E> = @VisitorStruct<E>;

pub fn default_visitor<E: Copy>() -> visitor<E> {
    return @VisitorStruct {
        visit_mod: |a,b,c,d|visit_mod::<E>(a, b, c, d),
        visit_view_item: |a,b|visit_view_item::<E>(a, b),
        visit_foreign_item: |a,b|visit_foreign_item::<E>(a, b),
        visit_item: |a,b|visit_item::<E>(a, b),
        visit_local: |a,b|visit_local::<E>(a, b),
        visit_block: |a,b|visit_block::<E>(a, b),
        visit_stmt: |a,b|visit_stmt::<E>(a, b),
        visit_arm: |a,b|visit_arm::<E>(a, b),
        visit_pat: |a,b|visit_pat::<E>(a, b),
        visit_decl: |a,b|visit_decl::<E>(a, b),
        visit_expr: |a,b|visit_expr::<E>(a, b),
        visit_expr_post: |_a,_b| (),
        visit_ty: |a,b|skip_ty::<E>(a, b),
        visit_generics: |a,b|visit_generics::<E>(a, b),
        visit_fn: |a,b,c,d,e,f|visit_fn::<E>(a, b, c, d, e, f),
        visit_ty_method: |a,b|visit_ty_method::<E>(a, b),
        visit_trait_method: |a,b|visit_trait_method::<E>(a, b),
        visit_struct_def: |a,b,c,d,e|visit_struct_def::<E>(a, b, c, d, e),
        visit_struct_field: |a,b|visit_struct_field::<E>(a, b),
        visit_struct_method: |a,b|visit_struct_method::<E>(a, b)
    };
}

trait Walk {
    fn walk_crate(&self, &crate);
    fn walk_mod(&self, &_mod, span, node_id);
    fn walk_view_item(&self, @view_item);
    fn walk_local(&self, loc: @local);
    fn walk_trait_ref(&self, @ast::trait_ref);
    fn walk_item(&self, @item);
    fn walk_enum_def(&self, &ast::enum_def, &Generics);
    fn walk_ty(&self, @Ty);
    fn walk_path(&self, @Path);
    fn walk_pat(&self, @pat);
    fn walk_foreign_item(&self, @foreign_item);
    fn walk_ty_param_bounds(&self, @OptVec<TyParamBound>);
    fn walk_generics(&self, &Generics);
    fn walk_fn_decl(&self, &fn_decl);
    fn walk_method_helper(&self, &method);
    fn walk_fn(&self, &fn_kind, &fn_decl, &blk, span, node_id);
    fn walk_ty_method(&self, &ty_method);
    fn walk_trait_method(&self, &trait_method);
    fn walk_struct_def(&self, @struct_def, ast::ident, &Generics, node_id);
    fn walk_struct_field(&self, @struct_field);
    fn walk_struct_method(&self, @method);
    fn walk_block(&self, &blk);
    fn walk_stmt(&self, @stmt);
    fn walk_decl(&self, @decl);
    fn walk_expr_opt(&self, Option<@expr>);
    fn walk_exprs(&self, &[@expr]);
    fn walk_mac(&self, &mac);
    fn walk_expr(&self, @expr);
    fn walk_arm(&self, &arm);
}

impl<'self> Walk for &'self Visitor {
    fn walk_crate(&self, c: &crate) {
        self.visit_mod(&c.node.module, c.span, crate_node_id);
    }

    fn walk_mod(&self, m: &_mod, _sp: span, _id: node_id) {
        for m.view_items.iter().advance |vi| { self.visit_view_item(*vi); }
        for m.items.iter().advance |i| { self.visit_item(*i); }
    }

    fn walk_view_item(&self, _vi: @view_item) { }

    fn walk_local(&self, loc: @local) {
        self.visit_pat(loc.node.pat);
        self.visit_ty(loc.node.ty);
        match loc.node.init {
            None => (),
            Some(ex) => self.visit_expr(ex)
        }
    }

    fn walk_trait_ref(&self, tref: @ast::trait_ref) {
        self.walk_path(tref.path);
    }

    fn walk_item(&self, i: @item) {
        match i.node {
            item_const(t, ex) => {
                self.visit_ty(t);
                self.visit_expr(ex);
            }
            item_fn(ref decl, purity, abi, ref generics, ref body) => {
                self.visit_fn(
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
            item_mod(ref m) => self.visit_mod(m, i.span, i.id),
            item_foreign_mod(ref nm) => {
                for nm.view_items.iter().advance |vi| { self.visit_view_item(*vi); }
                for nm.items.iter().advance |ni| { self.visit_foreign_item(*ni); }
            }
            item_ty(t, ref tps) => {
                self.visit_ty(t);
                self.visit_generics(tps);
            }
            item_enum(ref enum_definition, ref tps) => {
                self.visit_generics(tps);
                self.walk_enum_def(
                    enum_definition,
                    tps
                );
            }
            item_impl(ref tps, ref traits, ty, ref methods) => {
                self.visit_generics(tps);
                for traits.iter().advance |&p| {
                    self.walk_trait_ref(p);
                }
                self.visit_ty(ty);
                for methods.iter().advance |m| {
                    self.walk_method_helper(*m)
                }
            }
            item_struct(struct_def, ref generics) => {
                self.visit_generics(generics);
                self.visit_struct_def(struct_def, i.ident, generics, i.id);
            }
            item_trait(ref generics, ref traits, ref methods) => {
                self.visit_generics(generics);
                for traits.iter().advance |p| { self.walk_path(p.path); }
                for methods.iter().advance |m| {
                    self.visit_trait_method(m);
                }
            }
            item_mac(ref m) => self.walk_mac(m)
        }
    }

    fn walk_enum_def(&self, enum_definition: &ast::enum_def, tps: &Generics) {
        for enum_definition.variants.iter().advance |vr| {
            match vr.node.kind {
                tuple_variant_kind(ref variant_args) => {
                    for variant_args.iter().advance |va| { self.visit_ty(va.ty); }
                }
                struct_variant_kind(struct_def) => {
                    self.visit_struct_def(struct_def, vr.node.name, tps,
                                         vr.node.id);
                }
            }
            // Visit the disr expr if it exists
            for vr.node.disr_expr.iter().advance |ex| { self.visit_expr(*ex) }
        }
    }

    fn walk_ty(&self, t: @Ty) {
        match t.node {
            ty_box(mt) | ty_uniq(mt) |
            ty_vec(mt) | ty_ptr(mt) | ty_rptr(_, mt) => {
                self.visit_ty(mt.ty);
            },
            ty_tup(ref ts) => {
                for ts.iter().advance |tt| {
                    self.visit_ty(*tt);
                }
            },
            ty_closure(ref f) => {
                for f.decl.inputs.iter().advance |a| { self.visit_ty(a.ty); }
                self.visit_ty(f.decl.output);
            },
            ty_bare_fn(ref f) => {
                for f.decl.inputs.iter().advance |a| { self.visit_ty(a.ty); }
                self.visit_ty(f.decl.output);
            },
            ty_path(p, _) => self.walk_path(p),
            ty_fixed_length_vec(ref mt, ex) => {
                self.visit_ty(mt.ty);
                self.visit_expr(ex);
            },
            ty_nil | ty_bot | ty_mac(_) | ty_infer => ()
        }
    }

    fn walk_path(&self, p: @Path) {
        for p.types.iter().advance |tp| { self.visit_ty(*tp); }
    }

    fn walk_pat(&self, p: @pat) {
        match p.node {
            pat_enum(path, ref children) => {
                self.walk_path(path);
                for children.iter().advance |children| {
                    for children.iter().advance |child| { self.visit_pat(*child); }
                }
            }
            pat_struct(path, ref fields, _) => {
                self.walk_path(path);
                for fields.iter().advance |f| {
                    self.visit_pat(f.pat);
                }
            }
            pat_tup(ref elts) => {
                for elts.iter().advance |elt| {
                    self.visit_pat(*elt)
                }
            },
            pat_box(inner) | pat_uniq(inner) | pat_region(inner) => {
                self.visit_pat(inner)
            },
            pat_ident(_, path, ref inner) => {
                self.walk_path(path);
                for inner.iter().advance |subpat| { self.visit_pat(*subpat) }
            }
            pat_lit(ex) => self.visit_expr(ex),
            pat_range(e1, e2) => {
                self.visit_expr(e1);
                self.visit_expr(e2);
            }
            pat_wild => (),
            pat_vec(ref before, ref slice, ref after) => {
                for before.iter().advance |elt| {
                    self.visit_pat(*elt);
                }
                for slice.iter().advance |elt| {
                    self.visit_pat(*elt);
                }
                for after.iter().advance |tail| {
                    self.visit_pat(*tail);
                }
            }
        }
    }

    fn walk_foreign_item(&self, ni: @foreign_item) {
        match ni.node {
            foreign_item_fn(ref fd, _, ref generics) => {
                self.walk_fn_decl(fd);
                self.visit_generics(generics);
            }
            foreign_item_const(t) => {
                self.visit_ty(t);
            }
        }
    }

    fn walk_ty_param_bounds(&self, bounds: @OptVec<TyParamBound>) {
        for bounds.each |bound| {
            match *bound {
                TraitTyParamBound(ty) => self.walk_trait_ref(ty),
                RegionTyParamBound => {}
            }
        }
    }

    fn walk_generics(&self, generics: &Generics) {
        for generics.ty_params.each |tp| {
            self.walk_ty_param_bounds(tp.bounds);
        }
    }

    fn walk_fn_decl(&self, fd: &fn_decl) {
        for fd.inputs.iter().advance |a| {
            self.visit_pat(a.pat);
            self.visit_ty(a.ty);
        }
        self.visit_ty(fd.output);
    }

    // Note: there is no visit_method() method in the visitor, instead override
    // visit_fn() and check for fk_method().  This has the suffix _helper
    // because it is not a default impl of any method, though I doubt that really
    // clarifies anything. - Niko
    fn walk_method_helper(&self, m: &method) {
        self.visit_fn(
            &fk_method(
                /* FIXME (#2543) */ copy m.ident,
                &m.generics,
                m
            ),
            &m.decl,
            &m.body,
            m.span,
            m.id
        );
    }

    fn walk_fn(&self, fk: &fn_kind, decl: &fn_decl, body: &blk, _sp: span,
                        _id: node_id) {
        self.walk_fn_decl(decl);
        let generics = generics_of_fn(fk);
        self.visit_generics(&generics);
        self.visit_block(body);
    }

    fn walk_ty_method(&self, m: &ty_method) {
        for m.decl.inputs.iter().advance |a| { self.visit_ty(a.ty); }
        self.visit_generics(&m.generics);
        self.visit_ty(m.decl.output);
    }

    fn walk_trait_method(&self, m: &trait_method) {
        match *m {
            required(ref ty_m) => self.visit_ty_method(ty_m),
            provided(m) => self.walk_method_helper(m)
        }
    }

    fn walk_struct_def(&self,
        sd: @struct_def,
        _nm: ast::ident,
        _generics: &Generics,
        _id: node_id
    ) {
        for sd.fields.iter().advance |f| {
            self.visit_struct_field(*f);
        }
    }

    fn walk_struct_field(&self, sf: @struct_field) {
        self.visit_ty(sf.node.ty);
    }

    fn walk_struct_method(&self, m: @method) {
        self.walk_method_helper(m);
    }

    fn walk_block(&self, b: &blk) {
        for b.node.view_items.iter().advance |vi| {
            self.visit_view_item(*vi);
        }
        for b.node.stmts.iter().advance |s| {
            self.visit_stmt(*s);
        }
        self.walk_expr_opt(b.node.expr);
    }

    fn walk_stmt(&self, s: @stmt) {
        match s.node {
            stmt_decl(d, _) => self.visit_decl(d),
            stmt_expr(ex, _) => self.visit_expr(ex),
            stmt_semi(ex, _) => self.visit_expr(ex),
            stmt_mac(ref mac, _) => self.walk_mac(mac)
        }
    }

    fn walk_decl(&self, d: @decl) {
        match d.node {
            decl_local(ref loc) => self.visit_local(*loc),
            decl_item(it) => self.visit_item(it)
        }
    }

    fn walk_expr_opt(&self, eo: Option<@expr>) {
        match eo { None => (), Some(ex) => self.visit_expr(ex) }
    }

    fn walk_exprs(&self, exprs: &[@expr]) {
        for exprs.iter().advance |ex| { self.visit_expr(*ex); }
    }

    fn walk_mac(&self, _m: &mac) {
        /* no user-serviceable parts inside */
    }

    fn walk_expr(&self, ex: @expr) {
        match ex.node {
            expr_vstore(x, _) => self.visit_expr(x),
            expr_vec(ref es, _) => self.walk_exprs(*es),
            expr_repeat(element, count, _) => {
                self.visit_expr(element);
                self.visit_expr(count);
            }
            expr_struct(p, ref flds, base) => {
                self.walk_path(p);
                for flds.iter().advance |f| { self.visit_expr(f.node.expr); }
                self.walk_expr_opt(base);
            }
            expr_tup(ref elts) => {
                for elts.iter().advance |el| { self.visit_expr(*el) }
            }
            expr_call(callee, ref args, _) => {
                self.walk_exprs(*args);
                self.visit_expr(callee);
            }
            expr_method_call(_, callee, _, ref tys, ref args, _) => {
                self.walk_exprs(*args);
                for tys.iter().advance |tp| { self.visit_ty(*tp); }
                self.visit_expr(callee);
            }
            expr_binary(_, _, a, b) => {
                self.visit_expr(a);
                self.visit_expr(b);
            }
            expr_addr_of(_, x) | expr_unary(_, _, x) |
            expr_loop_body(x) | expr_do_body(x) => self.visit_expr(x),
            expr_lit(_) => (),
            expr_cast(x, t) => {
                self.visit_expr(x);
                self.visit_ty(t);
            }
            expr_if(x, ref b, eo) => {
                self.visit_expr(x);
                self.visit_block(b);
                self.walk_expr_opt(eo);
            }
            expr_while(x, ref b) => {
                self.visit_expr(x);
                self.visit_block(b);
            }
            expr_loop(ref b, _) => self.visit_block(b),
            expr_match(x, ref arms) => {
                self.visit_expr(x);
                for arms.iter().advance |a| { self.visit_arm(a); }
            }
            expr_fn_block(ref decl, ref body) => {
                self.visit_fn(
                    &fk_fn_block,
                    decl,
                    body,
                    ex.span,
                    ex.id
                );
            }
            expr_block(ref b) => self.visit_block(b),
            expr_assign(a, b) => {
                self.visit_expr(b);
                self.visit_expr(a);
            }
            expr_copy(a) => self.visit_expr(a),
            expr_assign_op(_, _, a, b) => {
                self.visit_expr(b);
                self.visit_expr(a);
            }
            expr_field(x, _, ref tys) => {
                self.visit_expr(x);
                for tys.iter().advance |tp| { self.visit_ty(*tp); }
            }
            expr_index(_, a, b) => {
                self.visit_expr(a);
                self.visit_expr(b);
            }
            expr_path(p) => self.walk_path(p),
            expr_self => (),
            expr_break(_) => (),
            expr_again(_) => (),
            expr_ret(eo) => self.walk_expr_opt(eo),
            expr_log(lv, x) => {
                self.visit_expr(lv);
                self.visit_expr(x);
            }
            expr_mac(ref mac) => self.walk_mac(mac),
            expr_paren(x) => self.visit_expr(x),
            expr_inline_asm(ref a) => {
                for a.inputs.iter().advance |&(_, in)| {
                    self.visit_expr(in);
                }
                for a.outputs.iter().advance |&(_, out)| {
                    self.visit_expr(out);
                }
            }
        }
        self.visit_expr_post(ex);
    }

    fn walk_arm(&self, a: &arm) {
        for a.pats.iter().advance |p| { self.visit_pat(*p); }
        self.walk_expr_opt(a.guard);
        self.visit_block(&a.body);
    }
}

fn walk_crate<V:Visitor>(v:&V, c: &crate) {
    v.visit_mod(&c.node.module, c.span, crate_node_id);
}

fn walk_mod<V:Visitor>(v:&V, m: &_mod, _sp: span, _id: node_id) {
    for m.view_items.iter().advance |vi| { v.visit_view_item(*vi); }
    for m.items.iter().advance |i| { v.visit_item(*i); }
}

fn walk_view_item<V:Visitor>(_v:&V, _vi: @view_item) { }

fn walk_local<V:Visitor>(v:&V, loc: @local) {
    v.visit_pat(loc.node.pat);
    v.visit_ty(loc.node.ty);
    match loc.node.init {
        None => (),
        Some(ex) => v.visit_expr(ex)
    }
}

fn walk_trait_ref<V:Visitor>(v:&V, tref: @ast::trait_ref) {
    walk_path(v, tref.path);
}

fn walk_item<V:Visitor>(v:&V, i: @item) {
    match i.node {
        item_const(t, ex) => {
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
            for nm.view_items.iter().advance |vi| { v.visit_view_item(*vi); }
            for nm.items.iter().advance |ni| { v.visit_foreign_item(*ni); }
        }
        item_ty(t, ref tps) => {
            v.visit_ty(t);
            v.visit_generics(tps);
        }
        item_enum(ref enum_definition, ref tps) => {
            v.visit_generics(tps);
            walk_enum_def(v, 
                enum_definition,
                tps
            );
        }
        item_impl(ref tps, ref traits, ty, ref methods) => {
            v.visit_generics(tps);
            for traits.iter().advance |&p| {
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
            for traits.iter().advance |p| { walk_path(v, p.path); }
            for methods.iter().advance |m| {
                v.visit_trait_method(m);
            }
        }
        item_mac(ref m) => walk_mac(v, m)
    }
}

fn walk_enum_def<V:Visitor>(v:&V, enum_definition: &ast::enum_def, tps: &Generics) {
    for enum_definition.variants.iter().advance |vr| {
        match vr.node.kind {
            tuple_variant_kind(ref variant_args) => {
                for variant_args.iter().advance |va| { v.visit_ty(va.ty); }
            }
            struct_variant_kind(struct_def) => {
                v.visit_struct_def(struct_def, vr.node.name, tps,
                                   vr.node.id);
            }
        }
        // Visit the disr expr if it exists
        for vr.node.disr_expr.iter().advance |ex| { v.visit_expr(*ex) }
    }
}

fn walk_ty<V:Visitor>(v:&V, t: @Ty) {
    match t.node {
        ty_box(mt) | ty_uniq(mt) |
        ty_vec(mt) | ty_ptr(mt) | ty_rptr(_, mt) => {
            v.visit_ty(mt.ty);
        },
        ty_tup(ref ts) => {
            for ts.iter().advance |tt| {
                v.visit_ty(*tt);
            }
        },
        ty_closure(ref f) => {
            for f.decl.inputs.iter().advance |a| { v.visit_ty(a.ty); }
            v.visit_ty(f.decl.output);
        },
        ty_bare_fn(ref f) => {
            for f.decl.inputs.iter().advance |a| { v.visit_ty(a.ty); }
            v.visit_ty(f.decl.output);
        },
        ty_path(p, _) => walk_path(v, p),
        ty_fixed_length_vec(ref mt, ex) => {
            v.visit_ty(mt.ty);
            v.visit_expr(ex);
        },
        ty_nil | ty_bot | ty_mac(_) | ty_infer => ()
    }
}

fn walk_path<V:Visitor>(v:&V, p: @Path) {
    for p.types.iter().advance |tp| { v.visit_ty(*tp); }
}

fn walk_pat<V:Visitor>(v:&V, p: @pat) {
    match p.node {
        pat_enum(path, ref children) => {
            walk_path(v, path);
            for children.iter().advance |children| {
                for children.iter().advance |child| { v.visit_pat(*child); }
            }
        }
        pat_struct(path, ref fields, _) => {
            walk_path(v, path);
            for fields.iter().advance |f| {
                v.visit_pat(f.pat);
            }
        }
        pat_tup(ref elts) => {
            for elts.iter().advance |elt| {
                v.visit_pat(*elt)
            }
        },
        pat_box(inner) | pat_uniq(inner) | pat_region(inner) => {
            v.visit_pat(inner)
        },
        pat_ident(_, path, ref inner) => {
            walk_path(v, path);
            for inner.iter().advance |subpat| { v.visit_pat(*subpat) }
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

fn walk_foreign_item<V:Visitor>(v:&V, ni: @foreign_item) {
    match ni.node {
        foreign_item_fn(ref fd, _, ref generics) => {
            walk_fn_decl(v, fd);
            v.visit_generics(generics);
        }
        foreign_item_const(t) => {
            v.visit_ty(t);
        }
    }
}

fn walk_ty_param_bounds<V:Visitor>(v:&V, bounds: @OptVec<TyParamBound>) {
    for bounds.each |bound| {
        match *bound {
            TraitTyParamBound(ty) => walk_trait_ref(v, ty),
            RegionTyParamBound => {}
        }
    }
}

fn walk_generics<V:Visitor>(v:&V, generics: &Generics) {
    for generics.ty_params.each |tp| {
        walk_ty_param_bounds(v, tp.bounds);
    }
}

fn walk_fn_decl<V:Visitor>(v:&V, fd: &fn_decl) {
    for fd.inputs.iter().advance |a| {
        v.visit_pat(a.pat);
        v.visit_ty(a.ty);
    }
    v.visit_ty(fd.output);
}

// Note: there is no visit_method() method in the visitor, instead override
// visit_fn() and check for fk_method().  This has the suffix _helper
// because it is not a default impl of any method, though I doubt that really
// clarifies anything. - Niko
fn walk_method_helper<V:Visitor>(v:&V, m: &method) {
    v.visit_fn(
        &fk_method(
            /* FIXME (#2543) */ copy m.ident,
            &m.generics,
            m
        ),
        &m.decl,
        &m.body,
        m.span,
        m.id
    );
}

fn walk_fn<V:Visitor>(v:&V, fk: &fn_kind, decl: &fn_decl, body: &blk, _sp: span,
                      _id: node_id) {
    walk_fn_decl(v, decl);
    let generics = generics_of_fn(fk);
    v.visit_generics(&generics);
    v.visit_block(body);
}

fn walk_ty_method<V:Visitor>(v:&V, m: &ty_method) {
    for m.decl.inputs.iter().advance |a| { v.visit_ty(a.ty); }
    v.visit_generics(&m.generics);
    v.visit_ty(m.decl.output);
}

fn walk_trait_method<V:Visitor>(v:&V, m: &trait_method) {
    match *m {
        required(ref ty_m) => v.visit_ty_method(ty_m),
        provided(m) => walk_method_helper(v, m)
    }
}

fn walk_struct_def<V:Visitor>(v:&V,
                              sd: @struct_def,
                              _nm: ast::ident,
                              _generics: &Generics,
                              _id: node_id
                             ) {
    for sd.fields.iter().advance |f| {
        v.visit_struct_field(*f);
    }
}

fn walk_struct_field<V:Visitor>(v:&V, sf: @struct_field) {
    v.visit_ty(sf.node.ty);
}

fn walk_struct_method<V:Visitor>(v:&V, m: @method) {
    walk_method_helper(v, m);
}

fn walk_block<V:Visitor>(v:&V, b: &blk) {
    for b.node.view_items.iter().advance |vi| {
        v.visit_view_item(*vi);
    }
    for b.node.stmts.iter().advance |s| {
        v.visit_stmt(*s);
    }
    walk_expr_opt(v, b.node.expr);
}

fn walk_stmt<V:Visitor>(v:&V, s: @stmt) {
    match s.node {
        stmt_decl(d, _) => v.visit_decl(d),
        stmt_expr(ex, _) => v.visit_expr(ex),
        stmt_semi(ex, _) => v.visit_expr(ex),
        stmt_mac(ref mac, _) => walk_mac(v, mac)
    }
}

fn walk_decl<V:Visitor>(v:&V, d: @decl) {
    match d.node {
        decl_local(ref loc) => v.visit_local(*loc),
        decl_item(it) => v.visit_item(it)
    }
}

fn walk_expr_opt<V:Visitor>(v:&V, eo: Option<@expr>) {
    match eo { None => (), Some(ex) => v.visit_expr(ex) }
}

fn walk_exprs<V:Visitor>(v:&V, exprs: &[@expr]) {
    for exprs.iter().advance |ex| { v.visit_expr(*ex); }
}

fn walk_mac<V:Visitor>(_v:&V, _m: &mac) {
    /* no user-serviceable parts inside */
}

fn walk_expr<V:Visitor>(v:&V, ex: @expr) {
    match ex.node {
        expr_vstore(x, _) => v.visit_expr(x),
        expr_vec(ref es, _) => walk_exprs(v, *es),
        expr_repeat(element, count, _) => {
            v.visit_expr(element);
            v.visit_expr(count);
        }
        expr_struct(p, ref flds, base) => {
            walk_path(v, p);
            for flds.iter().advance |f| { v.visit_expr(f.node.expr); }
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
            for tys.iter().advance |tp| { v.visit_ty(*tp); }
            v.visit_expr(callee);
        }
        expr_binary(_, _, a, b) => {
            v.visit_expr(a);
            v.visit_expr(b);
        }
        expr_addr_of(_, x) | expr_unary(_, _, x) |
        expr_loop_body(x) | expr_do_body(x) => v.visit_expr(x),
        expr_lit(_) => (),
        expr_cast(x, t) => {
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
        expr_copy(a) => v.visit_expr(a),
        expr_assign_op(_, _, a, b) => {
            v.visit_expr(b);
            v.visit_expr(a);
        }
        expr_field(x, _, ref tys) => {
            v.visit_expr(x);
            for tys.iter().advance |tp| { v.visit_ty(*tp); }
        }
        expr_index(_, a, b) => {
            v.visit_expr(a);
            v.visit_expr(b);
        }
        expr_path(p) => walk_path(v, p),
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

fn walk_arm<V:Visitor>(v:&V, a: &arm) {
    for a.pats.iter().advance |p| { v.visit_pat(*p); }
    walk_expr_opt(v, a.guard);
    v.visit_block(&a.body);
}

pub fn visit_crate<E: Copy>(c: &crate, (e, v): (E, vt<E>)) {
    (v.visit_mod)(&c.node.module, c.span, crate_node_id, (e, v));
}

pub fn visit_mod<E: Copy>(m: &_mod, _sp: span, _id: node_id, (e, v): (E, vt<E>)) {
    for m.view_items.iter().advance |vi| { (v.visit_view_item)(*vi, (copy e, v)); }
    for m.items.iter().advance |i| { (v.visit_item)(*i, (copy e, v)); }
}

pub fn visit_view_item<E>(_vi: @view_item, (_e, _v): (E, vt<E>)) { }

pub fn visit_local<E: Copy>(loc: @local, (e, v): (E, vt<E>)) {
    (v.visit_pat)(loc.node.pat, (copy e, v));
    (v.visit_ty)(loc.node.ty, (copy e, v));
    match loc.node.init {
      None => (),
      Some(ex) => (v.visit_expr)(ex, (e, v))
    }
}

fn visit_trait_ref<E: Copy>(tref: @ast::trait_ref, (e, v): (E, vt<E>)) {
    visit_path(tref.path, (e, v));
}

pub fn visit_item<E: Copy>(i: @item, (e, v): (E, vt<E>)) {
    match i.node {
        item_static(t, _, ex) => {
            (v.visit_ty)(t, (copy e, v));
            (v.visit_expr)(ex, (copy e, v));
        }
        item_fn(ref decl, purity, abi, ref generics, ref body) => {
            (v.visit_fn)(
                &fk_item_fn(
                    i.ident,
                    generics,
                    purity,
                    abi
                ),
                decl,
                body,
                i.span,
                i.id,
                (e,
                 v)
            );
        }
        item_mod(ref m) => (v.visit_mod)(m, i.span, i.id, (e, v)),
        item_foreign_mod(ref nm) => {
            for nm.view_items.iter().advance |vi| { (v.visit_view_item)(*vi, (copy e, v)); }
            for nm.items.iter().advance |ni| { (v.visit_foreign_item)(*ni, (copy e, v)); }
        }
        item_ty(t, ref tps) => {
            (v.visit_ty)(t, (copy e, v));
            (v.visit_generics)(tps, (e, v));
        }
        item_enum(ref enum_definition, ref tps) => {
            (v.visit_generics)(tps, (copy e, v));
            visit_enum_def(
                enum_definition,
                tps,
                (e, v)
            );
        }
        item_impl(ref tps, ref traits, ty, ref methods) => {
            (v.visit_generics)(tps, (copy e, v));
            for traits.iter().advance |&p| {
                visit_trait_ref(p, (copy e, v));
            }
            (v.visit_ty)(ty, (copy e, v));
            for methods.iter().advance |m| {
                visit_method_helper(*m, (copy e, v))
            }
        }
        item_struct(struct_def, ref generics) => {
            (v.visit_generics)(generics, (copy e, v));
            (v.visit_struct_def)(struct_def, i.ident, generics, i.id, (e, v));
        }
        item_trait(ref generics, ref traits, ref methods) => {
            (v.visit_generics)(generics, (copy e, v));
            for traits.iter().advance |p| { visit_path(p.path, (copy e, v)); }
            for methods.iter().advance |m| {
                (v.visit_trait_method)(m, (copy e, v));
            }
        }
        item_mac(ref m) => visit_mac(m, (e, v))
    }
}

pub fn visit_enum_def<E: Copy>(enum_definition: &ast::enum_def,
                               tps: &Generics,
                               (e, v): (E, vt<E>)) {
    for enum_definition.variants.iter().advance |vr| {
        match vr.node.kind {
            tuple_variant_kind(ref variant_args) => {
                for variant_args.iter().advance |va| {
                    (v.visit_ty)(va.ty, (copy e, v));
                }
            }
            struct_variant_kind(struct_def) => {
                (v.visit_struct_def)(struct_def, vr.node.name, tps,
                                     vr.node.id, (copy e, v));
            }
        }
        // Visit the disr expr if it exists
        for vr.node.disr_expr.iter().advance |ex| {
            (v.visit_expr)(*ex, (copy e, v))
        }
    }
}

pub fn skip_ty<E>(_t: @Ty, (_e,_v): (E, vt<E>)) {}

pub fn visit_ty<E: Copy>(t: @Ty, (e, v): (E, vt<E>)) {
    match t.node {
        ty_box(mt) | ty_uniq(mt) |
        ty_vec(mt) | ty_ptr(mt) | ty_rptr(_, mt) => {
            (v.visit_ty)(mt.ty, (e, v));
        },
        ty_tup(ref ts) => {
            for ts.iter().advance |tt| {
                (v.visit_ty)(*tt, (copy e, v));
            }
        },
        ty_closure(ref f) => {
            for f.decl.inputs.iter().advance |a| { (v.visit_ty)(a.ty, (copy e, v)); }
            (v.visit_ty)(f.decl.output, (copy e, v));
            visit_ty_param_bounds(&f.bounds, (e, v));
        },
        ty_bare_fn(ref f) => {
            for f.decl.inputs.iter().advance |a| { (v.visit_ty)(a.ty, (copy e, v)); }
            (v.visit_ty)(f.decl.output, (e, v));
        },
        ty_path(p, bounds, _) => {
            visit_path(p, (copy e, v));
            visit_ty_param_bounds(bounds, (e, v));
        },
        ty_fixed_length_vec(ref mt, ex) => {
            (v.visit_ty)(mt.ty, (copy e, v));
            (v.visit_expr)(ex, (copy e, v));
        },
        ty_nil | ty_bot | ty_mac(_) | ty_infer => ()
    }
}

pub fn visit_path<E: Copy>(p: @Path, (e, v): (E, vt<E>)) {
    for p.types.iter().advance |tp| { (v.visit_ty)(*tp, (copy e, v)); }
}

pub fn visit_pat<E: Copy>(p: @pat, (e, v): (E, vt<E>)) {
    match p.node {
        pat_enum(path, ref children) => {
            visit_path(path, (copy e, v));
            for children.iter().advance |children| {
                for children.iter().advance |child| {
                    (v.visit_pat)(*child, (copy e, v));
                }
            }
        }
        pat_struct(path, ref fields, _) => {
            visit_path(path, (copy e, v));
            for fields.iter().advance |f| {
                (v.visit_pat)(f.pat, (copy e, v));
            }
        }
        pat_tup(ref elts) => {
            for elts.iter().advance |elt| {
                (v.visit_pat)(*elt, (copy e, v))
            }
        },
        pat_box(inner) | pat_uniq(inner) | pat_region(inner) => {
            (v.visit_pat)(inner, (e, v))
        },
        pat_ident(_, path, ref inner) => {
            visit_path(path, (copy e, v));
            for inner.iter().advance |subpat| {
                (v.visit_pat)(*subpat, (copy e, v))
            }
        }
        pat_lit(ex) => (v.visit_expr)(ex, (e, v)),
        pat_range(e1, e2) => {
            (v.visit_expr)(e1, (copy e, v));
            (v.visit_expr)(e2, (e, v));
        }
        pat_wild => (),
        pat_vec(ref before, ref slice, ref after) => {
            for before.iter().advance |elt| {
                (v.visit_pat)(*elt, (copy e, v));
            }
            for slice.iter().advance |elt| {
                (v.visit_pat)(*elt, (copy e, v));
            }
            for after.iter().advance |tail| {
                (v.visit_pat)(*tail, (copy e, v));
            }
        }
    }
}

pub fn visit_foreign_item<E: Copy>(ni: @foreign_item, (e, v): (E, vt<E>)) {
    match ni.node {
        foreign_item_fn(ref fd, _, ref generics) => {
            visit_fn_decl(fd, (copy e, v));
            (v.visit_generics)(generics, (e, v));
        }
        foreign_item_static(t, _) => {
            (v.visit_ty)(t, (e, v));
        }
    }
}

pub fn visit_ty_param_bounds<E: Copy>(bounds: &OptVec<TyParamBound>,
                                      (e, v): (E, vt<E>)) {
    for bounds.each |bound| {
        match *bound {
            TraitTyParamBound(ty) => visit_trait_ref(ty, (copy e, v)),
            RegionTyParamBound => {}
        }
    }
}

pub fn visit_generics<E: Copy>(generics: &Generics, (e, v): (E, vt<E>)) {
    for generics.ty_params.each |tp| {
        visit_ty_param_bounds(tp.bounds, (copy e, v));
    }
}

pub fn visit_fn_decl<E: Copy>(fd: &fn_decl, (e, v): (E, vt<E>)) {
    for fd.inputs.iter().advance |a| {
        (v.visit_pat)(a.pat, (copy e, v));
        (v.visit_ty)(a.ty, (copy e, v));
    }
    (v.visit_ty)(fd.output, (e, v));
}

// Note: there is no visit_method() method in the visitor, instead override
// visit_fn() and check for fk_method().  I named this visit_method_helper()
// because it is not a default impl of any method, though I doubt that really
// clarifies anything. - Niko
pub fn visit_method_helper<E: Copy>(m: &method, (e, v): (E, vt<E>)) {
    (v.visit_fn)(
        &fk_method(
            /* FIXME (#2543) */ copy m.ident,
            &m.generics,
            m
        ),
        &m.decl,
        &m.body,
        m.span,
        m.id,
        (e, v)
    );
}

pub fn visit_fn<E: Copy>(fk: &fn_kind, decl: &fn_decl, body: &blk, _sp: span,
                         _id: node_id, (e, v): (E, vt<E>)) {
    visit_fn_decl(decl, (copy e, v));
    let generics = generics_of_fn(fk);
    (v.visit_generics)(&generics, (copy e, v));
    (v.visit_block)(body, (e, v));
}

pub fn visit_ty_method<E: Copy>(m: &ty_method, (e, v): (E, vt<E>)) {
    for m.decl.inputs.iter().advance |a| { (v.visit_ty)(a.ty, (copy e, v)); }
    (v.visit_generics)(&m.generics, (copy e, v));
    (v.visit_ty)(m.decl.output, (e, v));
}

pub fn visit_trait_method<E: Copy>(m: &trait_method, (e, v): (E, vt<E>)) {
    match *m {
      required(ref ty_m) => (v.visit_ty_method)(ty_m, (e, v)),
      provided(m) => visit_method_helper(m, (e, v))
    }
}

pub fn visit_struct_def<E: Copy>(
    sd: @struct_def,
    _nm: ast::ident,
    _generics: &Generics,
    _id: node_id,
    (e, v): (E, vt<E>)
) {
    for sd.fields.iter().advance |f| {
        (v.visit_struct_field)(*f, (copy e, v));
    }
}

pub fn visit_struct_field<E: Copy>(sf: @struct_field, (e, v): (E, vt<E>)) {
    (v.visit_ty)(sf.node.ty, (e, v));
}

pub fn visit_struct_method<E: Copy>(m: @method, (e, v): (E, vt<E>)) {
    visit_method_helper(m, (e, v));
}

pub fn visit_block<E: Copy>(b: &blk, (e, v): (E, vt<E>)) {
    for b.node.view_items.iter().advance |vi| {
        (v.visit_view_item)(*vi, (copy e, v));
    }
    for b.node.stmts.iter().advance |s| {
        (v.visit_stmt)(*s, (copy e, v));
    }
    visit_expr_opt(b.node.expr, (e, v));
}

pub fn visit_stmt<E>(s: @stmt, (e, v): (E, vt<E>)) {
    match s.node {
      stmt_decl(d, _) => (v.visit_decl)(d, (e, v)),
      stmt_expr(ex, _) => (v.visit_expr)(ex, (e, v)),
      stmt_semi(ex, _) => (v.visit_expr)(ex, (e, v)),
      stmt_mac(ref mac, _) => visit_mac(mac, (e, v))
    }
}

pub fn visit_decl<E: Copy>(d: @decl, (e, v): (E, vt<E>)) {
    match d.node {
        decl_local(ref loc) => (v.visit_local)(*loc, (e, v)),
        decl_item(it) => (v.visit_item)(it, (e, v))
    }
}

pub fn visit_expr_opt<E>(eo: Option<@expr>, (e, v): (E, vt<E>)) {
    match eo { None => (), Some(ex) => (v.visit_expr)(ex, (e, v)) }
}

pub fn visit_exprs<E: Copy>(exprs: &[@expr], (e, v): (E, vt<E>)) {
    for exprs.iter().advance |ex| { (v.visit_expr)(*ex, (copy e, v)); }
}

pub fn visit_mac<E>(_m: &mac, (_e, _v): (E, vt<E>)) {
    /* no user-serviceable parts inside */
}

pub fn visit_expr<E: Copy>(ex: @expr, (e, v): (E, vt<E>)) {
    match ex.node {
        expr_vstore(x, _) => (v.visit_expr)(x, (copy e, v)),
        expr_vec(ref es, _) => visit_exprs(*es, (copy e, v)),
        expr_repeat(element, count, _) => {
            (v.visit_expr)(element, (copy e, v));
            (v.visit_expr)(count, (copy e, v));
        }
        expr_struct(p, ref flds, base) => {
            visit_path(p, (copy e, v));
            for flds.iter().advance |f| {
                (v.visit_expr)(f.node.expr, (copy e, v));
            }
            visit_expr_opt(base, (copy e, v));
        }
        expr_tup(ref elts) => {
            for elts.iter().advance |el| { (v.visit_expr)(*el, (copy e, v)) }
        }
        expr_call(callee, ref args, _) => {
            visit_exprs(*args, (copy e, v));
            (v.visit_expr)(callee, (copy e, v));
        }
        expr_method_call(_, callee, _, ref tys, ref args, _) => {
            visit_exprs(*args, (copy e, v));
            for tys.iter().advance |tp| {
                (v.visit_ty)(*tp, (copy e, v));
            }
            (v.visit_expr)(callee, (copy e, v));
        }
        expr_binary(_, _, a, b) => {
            (v.visit_expr)(a, (copy e, v));
            (v.visit_expr)(b, (copy e, v));
        }
        expr_addr_of(_, x) | expr_unary(_, _, x) |
        expr_loop_body(x) | expr_do_body(x) => (v.visit_expr)(x, (copy e, v)),
        expr_lit(_) => (),
        expr_cast(x, t) => {
            (v.visit_expr)(x, (copy e, v));
            (v.visit_ty)(t, (copy e, v));
        }
        expr_if(x, ref b, eo) => {
            (v.visit_expr)(x, (copy e, v));
            (v.visit_block)(b, (copy e, v));
            visit_expr_opt(eo, (copy e, v));
        }
        expr_while(x, ref b) => {
            (v.visit_expr)(x, (copy e, v));
            (v.visit_block)(b, (copy e, v));
        }
        expr_loop(ref b, _) => (v.visit_block)(b, (copy e, v)),
        expr_match(x, ref arms) => {
            (v.visit_expr)(x, (copy e, v));
            for arms.iter().advance |a| { (v.visit_arm)(a, (copy e, v)); }
        }
        expr_fn_block(ref decl, ref body) => {
            (v.visit_fn)(
                &fk_fn_block,
                decl,
                body,
                ex.span,
                ex.id,
                (copy e, v)
            );
        }
        expr_block(ref b) => (v.visit_block)(b, (copy e, v)),
        expr_assign(a, b) => {
            (v.visit_expr)(b, (copy e, v));
            (v.visit_expr)(a, (copy e, v));
        }
        expr_copy(a) => (v.visit_expr)(a, (copy e, v)),
        expr_assign_op(_, _, a, b) => {
            (v.visit_expr)(b, (copy e, v));
            (v.visit_expr)(a, (copy e, v));
        }
        expr_field(x, _, ref tys) => {
            (v.visit_expr)(x, (copy e, v));
            for tys.iter().advance |tp| {
                (v.visit_ty)(*tp, (copy e, v));
            }
        }
        expr_index(_, a, b) => {
            (v.visit_expr)(a, (copy e, v));
            (v.visit_expr)(b, (copy e, v));
        }
        expr_path(p) => visit_path(p, (copy e, v)),
        expr_self => (),
        expr_break(_) => (),
        expr_again(_) => (),
        expr_ret(eo) => visit_expr_opt(eo, (copy e, v)),
        expr_log(lv, x) => {
            (v.visit_expr)(lv, (copy e, v));
            (v.visit_expr)(x, (copy e, v));
        }
        expr_mac(ref mac) => visit_mac(mac, (copy e, v)),
        expr_paren(x) => (v.visit_expr)(x, (copy e, v)),
        expr_inline_asm(ref a) => {
            for a.inputs.iter().advance |&(_, in)| {
                (v.visit_expr)(in, (copy e, v));
            }
            for a.outputs.iter().advance |&(_, out)| {
                (v.visit_expr)(out, (copy e, v));
            }
        }
    }
    (v.visit_expr_post)(ex, (e, v));
}

pub fn visit_arm<E: Copy>(a: &arm, (e, v): (E, vt<E>)) {
    for a.pats.iter().advance |p| { (v.visit_pat)(*p, (copy e, v)); }
    visit_expr_opt(a.guard, (copy e, v));
    (v.visit_block)(&a.body, (copy e, v));
}

// Simpler, non-context passing interface. Always walks the whole tree, simply
// calls the given functions on the nodes.

pub struct SimpleVisitor {
    visit_mod: @fn(&_mod, span, node_id),
    visit_view_item: @fn(@view_item),
    visit_foreign_item: @fn(@foreign_item),
    visit_item: @fn(@item),
    visit_local: @fn(@local),
    visit_block: @fn(&blk),
    visit_stmt: @fn(@stmt),
    visit_arm: @fn(&arm),
    visit_pat: @fn(@pat),
    visit_decl: @fn(@decl),
    visit_expr: @fn(@expr),
    visit_expr_post: @fn(@expr),
    visit_ty: @fn(@Ty),
    visit_generics: @fn(&Generics),
    visit_fn: @fn(&fn_kind, &fn_decl, &blk, span, node_id),
    visit_ty_method: @fn(&ty_method),
    visit_trait_method: @fn(&trait_method),
    visit_struct_def: @fn(@struct_def, ident, &Generics, node_id),
    visit_struct_field: @fn(@struct_field),
    visit_struct_method: @fn(@method)
}

pub type simple_visitor = @SimpleVisitor;

pub fn simple_ignore_ty(_t: @Ty) {}

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
        (e, v): ((), vt<()>)
    ) {
        f(m, sp, id);
        visit_mod(m, sp, id, (e, v));
    }
    fn v_view_item(f: @fn(@view_item), vi: @view_item, (e, v): ((), vt<()>)) {
        f(vi);
        visit_view_item(vi, (e, v));
    }
    fn v_foreign_item(f: @fn(@foreign_item), ni: @foreign_item, (e, v): ((), vt<()>)) {
        f(ni);
        visit_foreign_item(ni, (e, v));
    }
    fn v_item(f: @fn(@item), i: @item, (e, v): ((), vt<()>)) {
        f(i);
        visit_item(i, (e, v));
    }
    fn v_local(f: @fn(@local), l: @local, (e, v): ((), vt<()>)) {
        f(l);
        visit_local(l, (e, v));
    }
    fn v_block(f: @fn(&ast::blk), bl: &ast::blk, (e, v): ((), vt<()>)) {
        f(bl);
        visit_block(bl, (e, v));
    }
    fn v_stmt(f: @fn(@stmt), st: @stmt, (e, v): ((), vt<()>)) {
        f(st);
        visit_stmt(st, (e, v));
    }
    fn v_arm(f: @fn(&arm), a: &arm, (e, v): ((), vt<()>)) {
        f(a);
        visit_arm(a, (e, v));
    }
    fn v_pat(f: @fn(@pat), p: @pat, (e, v): ((), vt<()>)) {
        f(p);
        visit_pat(p, (e, v));
    }
    fn v_decl(f: @fn(@decl), d: @decl, (e, v): ((), vt<()>)) {
        f(d);
        visit_decl(d, (e, v));
    }
    fn v_expr(f: @fn(@expr), ex: @expr, (e, v): ((), vt<()>)) {
        f(ex);
        visit_expr(ex, (e, v));
    }
    fn v_expr_post(f: @fn(@expr), ex: @expr, (_e, _v): ((), vt<()>)) {
        f(ex);
    }
    fn v_ty(f: @fn(@Ty), ty: @Ty, (e, v): ((), vt<()>)) {
        f(ty);
        visit_ty(ty, (e, v));
    }
    fn v_ty_method(f: @fn(&ty_method), ty: &ty_method, (e, v): ((), vt<()>)) {
        f(ty);
        visit_ty_method(ty, (e, v));
    }
    fn v_trait_method(f: @fn(&trait_method),
                      m: &trait_method,
                      (e, v): ((), vt<()>)) {
        f(m);
        visit_trait_method(m, (e, v));
    }
    fn v_struct_def(
        f: @fn(@struct_def, ident, &Generics, node_id),
        sd: @struct_def,
        nm: ident,
        generics: &Generics,
        id: node_id,
        (e, v): ((), vt<()>)
    ) {
        f(sd, nm, generics, id);
        visit_struct_def(sd, nm, generics, id, (e, v));
    }
    fn v_generics(
        f: @fn(&Generics),
        ps: &Generics,
        (e, v): ((), vt<()>)
    ) {
        f(ps);
        visit_generics(ps, (e, v));
    }
    fn v_fn(
        f: @fn(&fn_kind, &fn_decl, &blk, span, node_id),
        fk: &fn_kind,
        decl: &fn_decl,
        body: &blk,
        sp: span,
        id: node_id,
        (e, v): ((), vt<()>)
    ) {
        f(fk, decl, body, sp, id);
        visit_fn(fk, decl, body, sp, id, (e, v));
    }
    let visit_ty: @fn(@Ty, ((), vt<()>)) =
        |a,b| v_ty(v.visit_ty, a, b);
    fn v_struct_field(f: @fn(@struct_field), sf: @struct_field, (e, v): ((), vt<()>)) {
        f(sf);
        visit_struct_field(sf, (e, v));
    }
    fn v_struct_method(f: @fn(@method), m: @method, (e, v): ((), vt<()>)) {
        f(m);
        visit_struct_method(m, (e, v));
    }
    return mk_vt(@VisitorStruct {
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
        visit_struct_method: |a,b|
            v_struct_method(v.visit_struct_method, a, b)
    });
}
