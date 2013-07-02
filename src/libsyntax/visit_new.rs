// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
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


pub enum FnKind<'self> {
    // fn foo() or extern "Abi" fn foo()
    FnKindItem(&'self ident, &'self Generics, purity, AbiSet),

    // fn foo(&self)
    FnKindMethod(&'self ident, &'self Generics, &'self method),

    // fn@(x, y) { ... }
    FnKindAnon(ast::Sigil),

    // |x, y| ...
    FnKindBlock,
}

static NO_GENERICS : Generics = Generics {
    lifetimes: opt_vec::Empty,
    ty_params: opt_vec::Empty,
};

#[allow(default_methods)]
impl<'self> FnKind<'self> {
    pub fn name(&self) -> ident {
        match self {
            &FnKindItem(name, _, _, _) |
            &FnKindMethod(name, _, _) => *name,
            &FnKindAnon(*) | &FnKindBlock(*) => parse::token::special_idents::anon
        }
    }

    pub fn generics<'r>(&'r self) -> &'r Generics {
        match self {
            &FnKindItem(_, generics, _, _) |
            &FnKindMethod(_, generics, _) => generics,
            &FnKindAnon(*) | &FnKindBlock(*) => &NO_GENERICS
        }
    }
}

#[allow(default_methods)]
pub trait Visitor {
    pub fn visit_crate(&mut self, c: &crate) {
        self.visit_mod(&c.node.module, c.span, crate_node_id)
    }

    pub fn visit_mod(&mut self, m: &_mod, sp: span, id: node_id) {
        self.visit_mod_contents(m, sp, id)
    }

    pub fn visit_mod_contents(&mut self, m: &_mod, _sp: span, _id: node_id) {
        for m.view_items.iter().advance |&vi| {
            self.visit_view_item(vi);
        }

        for m.items.iter().advance |&i| {
            self.visit_item(i);
        }
    }

    pub fn visit_view_item(&mut self, _vi: @view_item) { }

    pub fn visit_item(&mut self, i: @item) {
        self.visit_item_contents(i)
    }

    pub fn visit_item_contents(&mut self, i: @item) {
        match i.node {
            item_static(t, _, ex) => {
                self.visit_ty(t);
                self.visit_expr(ex);
            }
            item_fn(ref decl, purity, abi, ref generics, ref body) => {
                let fk = FnKindItem(&i.ident, generics, purity, abi);
                self.visit_fn(&fk, decl, body, i.span, i.id);
            }
            item_mod(ref m) => self.visit_mod(m, i.span, i.id),
                item_foreign_mod(ref nm) => {
                    for nm.view_items.iter().advance |&vi| {
                        self.visit_view_item(vi);
                    }
                    for nm.items.iter().advance |&fi| {
                        self.visit_foreign_item(fi);
                    }
                }
            item_ty(t, ref params) => {
                self.visit_ty(t);
                self.visit_generics(params);
            }
            item_enum(ref enum_definition, ref params) => {
                self.visit_generics(params);
                self.visit_enum_def(enum_definition, params);
            }
            item_impl(ref params, ref traits, ty, ref methods) => {
                self.visit_generics(params);
                for traits.iter().advance |p| {
                    self.visit_path(p.path);
                }
                self.visit_ty(ty);
                for methods.iter().advance |&m| {
                    let fk = FnKindMethod(&m.ident, &m.generics, m);
                    self.visit_fn(&fk, &m.decl, &m.body, m.span, m.id);
                }
            }
            item_struct(struct_def, ref generics) => {
                self.visit_generics(generics);
                self.visit_struct_def(struct_def, i.ident, generics, i.id);
            }
            item_trait(ref generics, ref traits, ref methods) => {
                self.visit_generics(generics);
                for traits.iter().advance |p| {
                    self.visit_path(p.path);
                }
                for methods.iter().advance |m| {
                    self.visit_trait_method(m);
                }
            }
            item_mac(ref m) => self.visit_mac(m)
        }
    }

    pub fn visit_local(&mut self, loc: @local) {
        self.visit_local_contents(loc)
    }

    pub fn visit_local_contents(&mut self, loc: @local) {
        self.visit_pat(loc.node.pat);
        self.visit_ty(loc.node.ty);

        match loc.node.init {
            None => (),
            Some(ex) => self.visit_expr(ex)
        }
    }

    pub fn visit_enum_def(&mut self, def: &enum_def, params: &Generics) {
        for def.variants.iter().advance |vr| {
            match vr.node.kind {
                tuple_variant_kind(ref args) => {
                    for args.iter().advance |va| {
                        self.visit_ty(va.ty);
                    }
                }
                struct_variant_kind(struct_def) => {
                    self.visit_struct_def(struct_def, vr.node.name, params, vr.node.id);
                }
            }

            for vr.node.disr_expr.iter().advance |&ex| {
                self.visit_expr(ex)
            }
        }
    }

    pub fn visit_ty(&mut self, t: @Ty) {
        self.visit_ty_contents(t)
    }

    pub fn visit_ty_contents(&mut self, t: @Ty) {
        match t.node {
            ty_box(mt) | ty_uniq(mt) | ty_vec(mt) |
                ty_ptr(mt) | ty_rptr(_, mt) => self.visit_ty(mt.ty),
                ty_tup(ref ts) => {
                    for ts.iter().advance |&tt| {
                        self.visit_ty(tt);
                    }
                }
            ty_closure(ref f) => {
                for f.decl.inputs.iter().advance |a| {
                    self.visit_ty(a.ty);
                }
                self.visit_ty(f.decl.output);
                match f.bounds {
                    Some(ref bounds) => self.visit_ty_param_bounds(bounds),
                    None => ()
                }
            }
            ty_bare_fn(ref f) => {
                for f.decl.inputs.iter().advance |a| {
                    self.visit_ty(a.ty);
                }
                self.visit_ty(f.decl.output);
            }
            ty_path(p, bounds, _) => {
                self.visit_path(p);
                match bounds {
                    @Some(ref bounds) => self.visit_ty_param_bounds(bounds),
                    @None => ()
                }
            }
            ty_fixed_length_vec(ref mt, ex) => {
                self.visit_ty(mt.ty);
                self.visit_expr(ex);
            }
            ty_nil | ty_bot | ty_mac(_) | ty_infer => ()
        }
    }

    pub fn visit_path(&mut self, p: @Path) {
        self.visit_path_contents(p);
    }

    pub fn visit_path_contents(&mut self, p: @Path) {
        for p.types.iter().advance |&tp| {
            self.visit_ty(tp);
        }
    }

    pub fn visit_pat(&mut self, p: @pat) {
        self.visit_pat_contents(p)
    }

    pub fn visit_pat_contents(&mut self, p: @pat) {
        match p.node {
            pat_enum(path, ref children) => {
                self.visit_path(path);
                for children.iter().advance |children| {
                    for children.iter().advance |&child| {
                        self.visit_pat(child);
                    }
                }
            }
            pat_struct(path, ref fields, _) => {
                self.visit_path(path);
                for fields.iter().advance |f| {
                    self.visit_pat(f.pat);
                }
            }
            pat_tup(ref elts) => {
                for elts.iter().advance |&elt| {
                    self.visit_pat(elt);
                }
            }
            pat_box(inner) | pat_uniq(inner) | pat_region(inner) => self.visit_pat(inner),
                pat_ident(_, path, ref inner) => {
                    self.visit_path(path);
                    for inner.iter().advance |&subpat| {
                        self.visit_pat(subpat);
                    }
                }
            pat_lit(ex) => self.visit_expr(ex),
                pat_range(e1, e2) => {
                    self.visit_expr(e1);
                    self.visit_expr(e2);
                }
            pat_wild => (),
            pat_vec(ref before, ref slice, ref after) => {
                for before.iter().advance |&elt| {
                    self.visit_pat(elt);
                }
                for slice.iter().advance |&elt| {
                    self.visit_pat(elt);
                }
                for after.iter().advance |&elt| {
                    self.visit_pat(elt);
                }
            }
        }
    }

    pub fn visit_foreign_item(&mut self, fi: @foreign_item) {
        self.visit_foreign_item_contents(fi)
    }

    pub fn visit_foreign_item_contents(&mut self, fi: @foreign_item) {
        match fi.node {
            foreign_item_fn(ref fd, _, ref generics) => {
                self.visit_fn_decl(fd);
                self.visit_generics(generics);
            }
            foreign_item_static(t, _) => {
                self.visit_ty(t);
            }
        }
    }

    pub fn visit_ty_param_bounds(&mut self, bounds: &OptVec<TyParamBound>) {
        self.visit_ty_param_bounds_contents(bounds);
    }

    pub fn visit_ty_param_bounds_contents(&mut self, bounds: &OptVec<TyParamBound>) {
        for bounds.iter().advance |bound| {
            match bound {
                &TraitTyParamBound(ty) => self.visit_path(ty.path),
                &RegionTyParamBound => ()
            }
        }
    }

    pub fn visit_generics(&mut self, generics: &Generics) {
        self.visit_generics_contents(generics)
    }

    pub fn visit_generics_contents(&mut self, generics: &Generics) {
        for generics.ty_params.iter().advance |tp| {
            self.visit_ty_param_bounds(tp.bounds);
        }
    }

    pub fn visit_fn_decl(&mut self, fd: &fn_decl) {
        self.visit_fn_decl_contents(fd)
    }

    pub fn visit_fn_decl_contents(&mut self, fd: &fn_decl) {
        for fd.inputs.iter().advance |a| {
            self.visit_pat(a.pat);
            self.visit_ty(a.ty);
        }
        self.visit_ty(fd.output);
    }

    pub fn visit_fn(&mut self, fk: &FnKind, decl: &fn_decl, body: &blk, sp: span, id: node_id) {
        self.visit_fn_contents(fk, decl, body, sp, id)
    }

    pub fn visit_fn_contents(&mut self, fk: &FnKind, decl: &fn_decl, body: &blk, _sp: span,
                             _id: node_id) {
        self.visit_fn_decl(decl);
        let generics = fk.generics();
        self.visit_generics(generics);
        self.visit_block(body);
    }

    pub fn visit_ty_method(&mut self, meth: &ty_method) {
        self.visit_ty_method_contents(meth);
    }

    pub fn visit_ty_method_contents(&mut self, meth: &ty_method) {
        for meth.decl.inputs.iter().advance |a| {
            self.visit_ty(a.ty);
        }
        self.visit_generics(&meth.generics);
        self.visit_ty(meth.decl.output);
    }

    pub fn visit_trait_method(&mut self, m: &trait_method) {
        self.visit_trait_method_contents(m)
    }

    pub fn visit_trait_method_contents(&mut self, m: &trait_method) {
        match m {
            &required(ref ty_m) => self.visit_ty_method(ty_m),
            &provided(m) => {
                let fk = FnKindMethod(&m.ident, &m.generics, m);
                self.visit_fn(&fk, &m.decl, &m.body, m.span, m.id);
            }
        }
    }

    pub fn visit_struct_def(&mut self, sd: @struct_def, nm: ast::ident,
                            generics: &Generics, id: node_id) {
        self.visit_struct_def_contents(sd, nm, generics, id)
    }

    pub fn visit_struct_def_contents(&mut self, sd: @struct_def, _nm: ast::ident,
                                     _generics: &Generics, _id: node_id) {
        for sd.fields.iter().advance |&f| {
            self.visit_struct_field(f)
        }
    }

    pub fn visit_struct_field(&mut self, sf: @struct_field) {
        self.visit_struct_field_contents(sf)
    }

    pub fn visit_struct_field_contents(&mut self, sf: @struct_field) {
        self.visit_ty(sf.node.ty)
    }

    pub fn visit_struct_method(&mut self, m: @method) {
        self.visit_struct_method_contents(m)
    }

    pub fn visit_struct_method_contents(&mut self, m: @method) {
        let fk = FnKindMethod(&m.ident, &m.generics, m);
        self.visit_fn(&fk, &m.decl, &m.body, m.span, m.id);
    }

    pub fn visit_block(&mut self, b: &blk) {
        self.visit_block_contents(b)
    }

    pub fn visit_block_contents(&mut self, b: &blk) {
        for b.node.view_items.iter().advance |&vi| {
            self.visit_view_item(vi);
        }
        for b.node.stmts.iter().advance |&s| {
            self.visit_stmt(s);
        }
        match b.node.expr {
            Some(ex) => self.visit_expr(ex),
            None => ()
        }
    }

    pub fn visit_stmt(&mut self, s: @stmt) {
        self.visit_stmt_contents(s)
    }

    pub fn visit_stmt_contents(&mut self, s: @stmt) {
        match s.node {
            stmt_decl(d, _) => self.visit_decl(d),
            stmt_semi(ex,_) | stmt_expr(ex, _) => self.visit_expr(ex),
            stmt_mac(ref mac, _) => self.visit_mac(mac),
        }
    }

    pub fn visit_decl(&mut self, d: @decl) {
        self.visit_decl_content(d)
    }

    pub fn visit_decl_content(&mut self, d: @decl) {
        match d.node {
            decl_local(ref loc) => self.visit_local(*loc),
            decl_item(it) => self.visit_item(it)
        }
    }

    pub fn visit_mac(&mut self, _m: &mac) { }

    pub fn visit_expr(&mut self, ex: @expr) {
        self.visit_expr_contents(ex)
    }

    pub fn visit_expr_contents(&mut self, ex: @expr) {
        match ex.node {
            expr_vstore(x, _) => self.visit_expr(x),
            expr_vec(ref es, _) => {
                for es.iter().advance |&ex| {
                    self.visit_expr(ex)
                }
            }
            expr_repeat(element, count, _) => {
                self.visit_expr(element);
                self.visit_expr(count);
            }
            expr_struct(p, ref flds, base) => {
                self.visit_path(p);
                for flds.iter().advance |f| {
                    self.visit_expr(f.node.expr);
                }
                match base {
                    Some(base) => self.visit_expr(base),
                    None => ()
                }
            }
            expr_tup(ref elts) => {
                for elts.iter().advance |&el| {
                    self.visit_expr(el);
                }
            }
            expr_call(callee, ref args, _) => {
                for args.iter().advance |&ex| {
                    self.visit_expr(ex);
                }
                self.visit_expr(callee);
            }
            expr_method_call(_, callee, _, ref tys, ref args, _) => {
                for args.iter().advance |&ex| {
                    self.visit_expr(ex);
                }
                for tys.iter().advance |&tp| {
                    self.visit_ty(tp);
                }
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
                match eo {
                    Some(ex) => self.visit_expr(ex),
                    None => ()
                }
            }
            expr_while(x, ref b) => {
                self.visit_expr(x);
                self.visit_block(b);
            }
            expr_loop(ref b, _) => self.visit_block(b),
            expr_match(x, ref arms) => {
                self.visit_expr(x);
                for arms.iter().advance |a| {
                    self.visit_arm(a);
                }
            }
            expr_fn_block(ref decl, ref body) => {
                self.visit_fn(&FnKindBlock, decl, body, ex.span, ex.id);
            }
            expr_block(ref b) => self.visit_block(b),
            expr_assign(a, b) => {
                self.visit_expr(b);
                self.visit_expr(a);
            }
            expr_copy(a) => self.visit_expr(a),
            expr_assign_op(_, _, a, b) => {
                self.visit_expr(a);
                self.visit_expr(b);
            }
            expr_field(x, _, ref tys) => {
                self.visit_expr(x);
                for tys.iter().advance |&tp| {
                    self.visit_ty(tp);
                }
            }
            expr_index(_, a, b) => {
                self.visit_expr(a);
                self.visit_expr(b);
            }
            expr_path(p) => self.visit_path(p),
            expr_self => (),
            expr_break(_) => (),
            expr_again(_) => (),
            expr_ret(Some(e)) => self.visit_expr(e),
            expr_ret(_) => (),
            expr_log(lv, x) => {
                self.visit_expr(lv);
                self.visit_expr(x);
            }
            expr_mac(ref mac) => self.visit_mac(mac),
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
        self.visit_expr_post(ex)
    }

    pub fn visit_expr_post(&mut self, _ex: @expr) { }

    pub fn visit_arm(&mut self, a: &arm) {
        self.visit_arm_contents(a)
    }

    pub fn visit_arm_contents(&mut self, a: &arm) {
        for a.pats.iter().advance |&p| {
            self.visit_pat(p);
        }
        match a.guard {
            Some(ex) => self.visit_expr(ex),
            None => ()
        }
        self.visit_block(&a.body);
    }

}
