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

pub trait Visitor {
    fn visit_mod(@mut self, m:&_mod, span, NodeId);
    fn visit_view_item(@mut self, &view_item);
    fn visit_foreign_item(@mut self, @foreign_item);
    fn visit_item(@mut self, @item);
    fn visit_local(@mut self, @Local);
    fn visit_block(@mut self, &Block);
    fn visit_stmt(@mut self, @stmt);
    fn visit_arm(@mut self, &arm);
    fn visit_pat(@mut self, @pat);
    fn visit_decl(@mut self, @decl);
    fn visit_expr(@mut self, @expr);
    fn visit_expr_post(@mut self, @expr);
    fn visit_ty(@mut self, &Ty);
    fn visit_generics(@mut self, &Generics);
    fn visit_fn(@mut self, &fn_kind, &fn_decl, &Block, span, NodeId);
    fn visit_ty_method(@mut self, &TypeMethod);
    fn visit_trait_method(@mut self, &trait_method);
    fn visit_struct_def(@mut self, @struct_def, ident, &Generics, NodeId);
    fn visit_struct_field(@mut self, @struct_field);

    fn env_clone(@mut self) -> @mut Visitor;
}

pub fn walk_crate(visitor: @mut Visitor, crate: &Crate) {
    visitor.visit_mod(&crate.module, crate.span, CRATE_NODE_ID)
}

pub fn walk_mod(visitor: @mut Visitor, module: &_mod) {
    for view_item in module.view_items.iter() {
        visitor.env_clone().visit_view_item(view_item)
    }
    for item in module.items.iter() {
        visitor.env_clone().visit_item(*item)
    }
}

pub fn walk_view_item(_: @mut Visitor, _: &view_item) {
    // Empty!
}

pub fn walk_local(visitor: @mut Visitor, local: &Local) {
    visitor.env_clone().visit_pat(local.pat);
    visitor.env_clone().visit_ty(&local.ty);
    match local.init {
        None => {}
        Some(initializer) => visitor.visit_expr(initializer),
    }
}

fn walk_trait_ref(visitor: @mut Visitor,
                   trait_ref: &ast::trait_ref) {
    walk_path(visitor, &trait_ref.path)
}

pub fn walk_item(visitor: @mut Visitor, item: &item) {
    match item.node {
        item_static(ref typ, _, expr) => {
            visitor.env_clone().visit_ty(typ);
            visitor.visit_expr(expr);
        }
        item_fn(ref declaration, purity, abi, ref generics, ref body) => {
            visitor.visit_fn(&fk_item_fn(item.ident, generics, purity, abi),
                             declaration,
                             body,
                             item.span,
                             item.id)
        }
        item_mod(ref module) => {
            visitor.visit_mod(module, item.span, item.id)
        }
        item_foreign_mod(ref foreign_module) => {
            for view_item in foreign_module.view_items.iter() {
                visitor.env_clone().visit_view_item(view_item)
            }
            for foreign_item in foreign_module.items.iter() {
                visitor.env_clone().visit_foreign_item(*foreign_item)
            }
        }
        item_ty(ref typ, ref type_parameters) => {
            visitor.env_clone().visit_ty(typ);
            visitor.visit_generics(type_parameters)
        }
        item_enum(ref enum_definition, ref type_parameters) => {
            visitor.env_clone().visit_generics(type_parameters);
            walk_enum_def(visitor, enum_definition, type_parameters)
        }
        item_impl(ref type_parameters,
                  ref trait_references,
                  ref typ,
                  ref methods) => {
            visitor.env_clone().visit_generics(type_parameters);
            for trait_reference in trait_references.iter() {
                walk_trait_ref(visitor.env_clone(), trait_reference)
            }
            visitor.env_clone().visit_ty(typ);
            for method in methods.iter() {
                walk_method_helper(visitor.env_clone(), *method)
            }
        }
        item_struct(struct_definition, ref generics) => {
            visitor.env_clone().visit_generics(generics);
            visitor.visit_struct_def(struct_definition,
                                     item.ident,
                                     generics,
                                     item.id)
        }
        item_trait(ref generics, ref trait_paths, ref methods) => {
            visitor.env_clone().visit_generics(generics);
            for trait_path in trait_paths.iter() {
                walk_path(visitor.env_clone(), &trait_path.path)
            }
            for method in methods.iter() {
                visitor.env_clone().visit_trait_method(method)
            }
        }
        item_mac(ref macro) => walk_mac(visitor, macro),
    }
}

pub fn walk_enum_def(visitor: @mut Visitor,
                     enum_definition: &ast::enum_def,
                     generics: &Generics) {
    for variant in enum_definition.variants.iter() {
        match variant.node.kind {
            tuple_variant_kind(ref variant_arguments) => {
                for variant_argument in variant_arguments.iter() {
                    visitor.env_clone().visit_ty(&variant_argument.ty)
                }
            }
            struct_variant_kind(struct_definition) => {
                visitor.env_clone().visit_struct_def(struct_definition,
                                                     variant.node.name,
                                                     generics,
                                                     variant.node.id)
            }
        }
    }
}

pub fn skip_ty(_: @mut Visitor, _: &Ty) {
    // Empty!
}

pub fn walk_ty(visitor: @mut Visitor, typ: &Ty) {
    match typ.node {
        ty_box(ref mutable_type) | ty_uniq(ref mutable_type) |
        ty_vec(ref mutable_type) | ty_ptr(ref mutable_type) |
        ty_rptr(_, ref mutable_type) => {
            visitor.visit_ty(mutable_type.ty)
        }
        ty_tup(ref tuple_element_types) => {
            for tuple_element_type in tuple_element_types.iter() {
                visitor.env_clone().visit_ty(tuple_element_type)
            }
        }
        ty_closure(ref function_declaration) => {
            for argument in function_declaration.decl.inputs.iter() {
                visitor.env_clone().visit_ty(&argument.ty)
            }
            visitor.env_clone().visit_ty(&function_declaration.decl.output);
            for bounds in function_declaration.bounds.iter() {
                walk_ty_param_bounds(visitor.env_clone(), bounds)
            }
        }
        ty_bare_fn(ref function_declaration) => {
            for argument in function_declaration.decl.inputs.iter() {
                visitor.env_clone().visit_ty(&argument.ty)
            }
            visitor.env_clone().visit_ty(&function_declaration.decl.output)
        }
        ty_path(ref path, ref bounds, _) => {
            walk_path(visitor.env_clone(), path);
            for bounds in bounds.iter() {
                walk_ty_param_bounds(visitor.env_clone(), bounds)
            }
        }
        ty_fixed_length_vec(ref mutable_type, expression) => {
            visitor.env_clone().visit_ty(mutable_type.ty);
            visitor.visit_expr(expression)
        }
        ty_nil | ty_bot | ty_mac(_) | ty_infer => ()
    }
}

pub fn walk_path(visitor: @mut Visitor, path: &Path) {
    for typ in path.types.iter() {
        visitor.env_clone().visit_ty(typ)
    }
}

pub fn walk_pat(visitor: @mut Visitor, pattern: &pat) {
    match pattern.node {
        pat_enum(ref path, ref children) => {
            walk_path(visitor.env_clone(), path);
            for children in children.iter() {
                for child in children.iter() {
                    visitor.env_clone().visit_pat(*child)
                }
            }
        }
        pat_struct(ref path, ref fields, _) => {
            walk_path(visitor.env_clone(), path);
            for field in fields.iter() {
                visitor.env_clone().visit_pat(field.pat)
            }
        }
        pat_tup(ref tuple_elements) => {
            for tuple_element in tuple_elements.iter() {
                visitor.env_clone().visit_pat(*tuple_element)
            }
        }
        pat_box(subpattern) |
        pat_uniq(subpattern) |
        pat_region(subpattern) => {
            visitor.visit_pat(subpattern)
        }
        pat_ident(_, ref path, ref optional_subpattern) => {
            walk_path(visitor.env_clone(), path);
            match *optional_subpattern {
                None => {}
                Some(subpattern) => visitor.visit_pat(subpattern),
            }
        }
        pat_lit(expression) => visitor.visit_expr(expression),
        pat_range(lower_bound, upper_bound) => {
            visitor.env_clone().visit_expr(lower_bound);
            visitor.visit_expr(upper_bound)
        }
        pat_wild => (),
        pat_vec(ref prepattern, ref slice_pattern, ref postpatterns) => {
            for prepattern in prepattern.iter() {
                visitor.env_clone().visit_pat(*prepattern)
            }
            for slice_pattern in slice_pattern.iter() {
                visitor.env_clone().visit_pat(*slice_pattern)
            }
            for postpattern in postpatterns.iter() {
                visitor.env_clone().visit_pat(*postpattern)
            }
        }
    }
}

pub fn walk_foreign_item(visitor: @mut Visitor,
                         foreign_item: &foreign_item) {
    match foreign_item.node {
        foreign_item_fn(ref function_declaration, ref generics) => {
            walk_fn_decl(visitor.env_clone(), function_declaration);
            visitor.visit_generics(generics)
        }
        foreign_item_static(ref typ, _) => visitor.visit_ty(typ),
    }
}

pub fn walk_ty_param_bounds(visitor: @mut Visitor,
                             bounds: &OptVec<TyParamBound>) {
    for bound in bounds.iter() {
        match *bound {
            TraitTyParamBound(ref typ) => {
                walk_trait_ref(visitor.env_clone(), typ)
            }
            RegionTyParamBound => {}
        }
    }
}

pub fn walk_generics(visitor: @mut Visitor,
                      generics: &Generics) {
    for type_parameter in generics.ty_params.iter() {
        walk_ty_param_bounds(visitor.env_clone(), &type_parameter.bounds)
    }
}

pub fn walk_fn_decl(visitor: @mut Visitor,
                     function_declaration: &fn_decl) {
    for argument in function_declaration.inputs.iter() {
        visitor.env_clone().visit_pat(argument.pat);
        visitor.env_clone().visit_ty(&argument.ty)
    }
    visitor.visit_ty(&function_declaration.output)
}

// Note: there is no visit_method() method in the visitor, instead override
// visit_fn() and check for fk_method().  I named this visit_method_helper()
// because it is not a default impl of any method, though I doubt that really
// clarifies anything. - Niko
pub fn walk_method_helper(visitor: @mut Visitor,
                           method: &method) {
    visitor.visit_fn(&fk_method(method.ident, &method.generics, method),
                     &method.decl,
                     &method.body,
                     method.span,
                     method.id)
}

pub fn walk_fn(visitor: @mut Visitor,
                function_kind: &fn_kind,
                function_declaration: &fn_decl,
                function_body: &Block,
                _: span,
                _: NodeId) {
    walk_fn_decl(visitor.env_clone(), function_declaration);
    let generics = generics_of_fn(function_kind);
    visitor.env_clone().visit_generics(&generics);
    visitor.visit_block(function_body)
}

pub fn walk_ty_method(visitor: @mut Visitor,
                       method_type: &TypeMethod) {
    for argument_type in method_type.decl.inputs.iter() {
        visitor.env_clone().visit_ty(&argument_type.ty)
    }
    visitor.env_clone().visit_generics(&method_type.generics);
    visitor.env_clone().visit_ty(&method_type.decl.output)
}

pub fn walk_trait_method(visitor: @mut Visitor,
                          trait_method: &trait_method) {
    match *trait_method {
        required(ref method_type) => {
            visitor.visit_ty_method(method_type)
        }
        provided(method) => walk_method_helper(visitor, method),
    }
}

pub fn walk_struct_def(visitor: @mut Visitor,
                        struct_definition: @struct_def,
                        _: ast::ident,
                        _: &Generics,
                        _: NodeId) {
    for field in struct_definition.fields.iter() {
        visitor.env_clone().visit_struct_field(*field)
    }
}

pub fn walk_struct_field(visitor: @mut Visitor,
                          struct_field: &struct_field) {
    visitor.visit_ty(&struct_field.node.ty)
}

pub fn walk_block(visitor: @mut Visitor, block: &Block) {
    for view_item in block.view_items.iter() {
        visitor.env_clone().visit_view_item(view_item)
    }
    for statement in block.stmts.iter() {
        visitor.env_clone().visit_stmt(*statement)
    }
    walk_expr_opt(visitor, block.expr)
}

pub fn walk_stmt(visitor: @mut Visitor, statement: &stmt) {
    match statement.node {
        stmt_decl(declaration, _) => visitor.visit_decl(declaration),
        stmt_expr(expression, _) | stmt_semi(expression, _) => {
            visitor.visit_expr(expression)
        }
        stmt_mac(ref macro, _) => walk_mac(visitor, macro),
    }
}

pub fn walk_decl(visitor: @mut Visitor, declaration: &decl) {
    match declaration.node {
        decl_local(ref local) => visitor.visit_local(*local),
        decl_item(item) => visitor.visit_item(item),
    }
}

pub fn walk_expr_opt(visitor: @mut Visitor,
                      optional_expression: Option<@expr>) {
    match optional_expression {
        None => {}
        Some(expression) => visitor.visit_expr(expression),
    }
}

pub fn walk_exprs(visitor: @mut Visitor,
                   expressions: &[@expr]) {
    for expression in expressions.iter() {
        visitor.env_clone().visit_expr(*expression)
    }
}

pub fn walk_mac(_: @mut Visitor, _: &mac) {
    // Empty!
}

pub fn walk_expr(visitor: @mut Visitor, expression: @expr) {
    match expression.node {
        expr_vstore(subexpression, _) => {
            visitor.env_clone().visit_expr(subexpression)
        }
        expr_vec(ref subexpressions, _) => {
            walk_exprs(visitor.env_clone(), *subexpressions)
        }
        expr_repeat(element, count, _) => {
            visitor.env_clone().visit_expr(element);
            visitor.env_clone().visit_expr(count)
        }
        expr_struct(ref path, ref fields, optional_base) => {
            walk_path(visitor.env_clone(), path);
            for field in fields.iter() {
                visitor.env_clone().visit_expr(field.expr)
            }
            walk_expr_opt(visitor.env_clone(), optional_base)
        }
        expr_tup(ref subexpressions) => {
            for subexpression in subexpressions.iter() {
                visitor.env_clone().visit_expr(*subexpression)
            }
        }
        expr_call(callee_expression, ref arguments, _) => {
            for argument in arguments.iter() {
                visitor.env_clone().visit_expr(*argument)
            }
            visitor.env_clone().visit_expr(callee_expression)
        }
        expr_method_call(_, callee, _, ref types, ref arguments, _) => {
            walk_exprs(visitor.env_clone(), *arguments);
            for typ in types.iter() {
                visitor.env_clone().visit_ty(typ)
            }
            visitor.env_clone().visit_expr(callee)
        }
        expr_binary(_, _, left_expression, right_expression) => {
            visitor.env_clone().visit_expr(left_expression);
            visitor.env_clone().visit_expr(right_expression)
        }
        expr_addr_of(_, subexpression) |
        expr_unary(_, _, subexpression) |
        expr_do_body(subexpression) => {
            visitor.env_clone().visit_expr(subexpression)
        }
        expr_lit(_) => {}
        expr_cast(subexpression, ref typ) => {
            visitor.env_clone().visit_expr(subexpression);
            visitor.env_clone().visit_ty(typ)
        }
        expr_if(head_expression, ref if_block, optional_else) => {
            visitor.env_clone().visit_expr(head_expression);
            visitor.env_clone().visit_block(if_block);
            walk_expr_opt(visitor.env_clone(), optional_else)
        }
        expr_while(subexpression, ref block) => {
            visitor.env_clone().visit_expr(subexpression);
            visitor.env_clone().visit_block(block)
        }
        expr_for_loop(pattern, subexpression, ref block) => {
            visitor.env_clone().visit_pat(pattern);
            visitor.env_clone().visit_expr(subexpression);
            visitor.env_clone().visit_block(block)
        }
        expr_loop(ref block, _) => visitor.env_clone().visit_block(block),
        expr_match(subexpression, ref arms) => {
            visitor.env_clone().visit_expr(subexpression);
            for arm in arms.iter() {
                visitor.env_clone().visit_arm(arm)
            }
        }
        expr_fn_block(ref function_declaration, ref body) => {
            visitor.env_clone().visit_fn(&fk_fn_block,
                                         function_declaration,
                                         body,
                                         expression.span,
                                         expression.id)
        }
        expr_block(ref block) => visitor.env_clone().visit_block(block),
        expr_assign(left_hand_expression, right_hand_expression) => {
            visitor.env_clone().visit_expr(right_hand_expression);
            visitor.env_clone().visit_expr(left_hand_expression)
        }
        expr_assign_op(_, _, left_expression, right_expression) => {
            visitor.env_clone().visit_expr(right_expression);
            visitor.env_clone().visit_expr(left_expression)
        }
        expr_field(subexpression, _, ref types) => {
            visitor.env_clone().visit_expr(subexpression);
            for typ in types.iter() {
                visitor.env_clone().visit_ty(typ)
            }
        }
        expr_index(_, main_expression, index_expression) => {
            visitor.env_clone().visit_expr(main_expression);
            visitor.env_clone().visit_expr(index_expression)
        }
        expr_path(ref path) => walk_path(visitor.env_clone(), path),
        expr_self | expr_break(_) | expr_again(_) => {}
        expr_ret(optional_expression) => {
            walk_expr_opt(visitor.env_clone(), optional_expression)
        }
        expr_log(level, subexpression) => {
            visitor.env_clone().visit_expr(level);
            visitor.env_clone().visit_expr(subexpression);
        }
        expr_mac(ref macro) => walk_mac(visitor.env_clone(), macro),
        expr_paren(subexpression) => {
            visitor.env_clone().visit_expr(subexpression)
        }
        expr_inline_asm(ref assembler) => {
            for &(_, input) in assembler.inputs.iter() {
                visitor.env_clone().visit_expr(input)
            }
            for &(_, output) in assembler.outputs.iter() {
                visitor.env_clone().visit_expr(output)
            }
        }
    }

    visitor.env_clone().visit_expr_post(expression)
}

pub fn walk_arm(visitor: @mut Visitor, arm: &arm) {
    for pattern in arm.pats.iter() {
        visitor.env_clone().visit_pat(*pattern)
    }
    walk_expr_opt(visitor.env_clone(), arm.guard);
    visitor.visit_block(&arm.body)
}

// Simpler, non-context passing interface. Always walks the whole tree, simply
// calls the given functions on the nodes.

pub trait SimpleVisitor {
    fn visit_mod(@mut self, &_mod, span, NodeId);
    fn visit_view_item(@mut self, &view_item);
    fn visit_foreign_item(@mut self, @foreign_item);
    fn visit_item(@mut self, @item);
    fn visit_local(@mut self, @Local);
    fn visit_block(@mut self, &Block);
    fn visit_stmt(@mut self, @stmt);
    fn visit_arm(@mut self, &arm);
    fn visit_pat(@mut self, @pat);
    fn visit_decl(@mut self, @decl);
    fn visit_expr(@mut self, @expr);
    fn visit_expr_post(@mut self, @expr);
    fn visit_ty(@mut self, &Ty);
    fn visit_generics(@mut self, &Generics);
    fn visit_fn(@mut self, &fn_kind, &fn_decl, &Block, span, NodeId);
    fn visit_ty_method(@mut self, &TypeMethod);
    fn visit_trait_method(@mut self, &trait_method);
    fn visit_struct_def(@mut self, @struct_def, ident, &Generics, NodeId);
    fn visit_struct_field(@mut self, @struct_field);
    fn visit_struct_method(@mut self, @method);
}

pub struct SimpleVisitorVisitor {
    simple_visitor: @SimpleVisitor,
}

impl Visitor for SimpleVisitorVisitor {
    fn env_clone(@mut self) -> @mut Visitor { self as @mut Visitor }

    fn visit_mod(@mut self,
                 module: &_mod,
                 span: span,
                 node_id: NodeId) {
        self.simple_visitor.visit_mod(module, span, node_id);
        walk_mod(self as @mut Visitor, module)
    }
    fn visit_view_item(@mut self, view_item: &view_item) {
        self.simple_visitor.visit_view_item(view_item);
        walk_view_item(self as @mut Visitor, view_item)
    }
    fn visit_foreign_item(@mut self, foreign_item: @foreign_item) {
        self.simple_visitor.visit_foreign_item(foreign_item);
        walk_foreign_item(self as @mut Visitor, foreign_item)
    }
    fn visit_item(@mut self, item: @item) {
        self.simple_visitor.visit_item(item);
        walk_item(self as @mut Visitor, item)
    }
    fn visit_local(@mut self, local: @Local) {
        self.simple_visitor.visit_local(local);
        walk_local(self as @mut Visitor, local)
    }
    fn visit_block(@mut self, block: &Block) {
        self.simple_visitor.visit_block(block);
        walk_block(self as @mut Visitor, block)
    }
    fn visit_stmt(@mut self, statement: @stmt) {
        self.simple_visitor.visit_stmt(statement);
        walk_stmt(self as @mut Visitor, statement)
    }
    fn visit_arm(@mut self, arm: &arm) {
        self.simple_visitor.visit_arm(arm);
        walk_arm(self as @mut Visitor, arm)
    }
    fn visit_pat(@mut self, pattern: @pat) {
        self.simple_visitor.visit_pat(pattern);
        walk_pat(self as @mut Visitor, pattern)
    }
    fn visit_decl(@mut self, declaration: @decl) {
        self.simple_visitor.visit_decl(declaration);
        walk_decl(self as @mut Visitor, declaration)
    }
    fn visit_expr(@mut self, expression: @expr) {
        self.simple_visitor.visit_expr(expression);
        walk_expr(self as @mut Visitor, expression)
    }
    fn visit_expr_post(@mut self, expression: @expr) {
        self.simple_visitor.visit_expr_post(expression)
    }
    fn visit_ty(@mut self, typ: &Ty) {
        self.simple_visitor.visit_ty(typ);
        walk_ty(self as @mut Visitor, typ)
    }
    fn visit_generics(@mut self, generics: &Generics) {
        self.simple_visitor.visit_generics(generics);
        walk_generics(self as @mut Visitor, generics)
    }
    fn visit_fn(@mut self,
                function_kind: &fn_kind,
                function_declaration: &fn_decl,
                block: &Block,
                span: span,
                node_id: NodeId) {
        self.simple_visitor.visit_fn(function_kind,
                                     function_declaration,
                                     block,
                                     span,
                                     node_id);
        walk_fn(self as @mut Visitor,
                 function_kind,
                 function_declaration,
                 block,
                 span,
                 node_id)
    }
    fn visit_ty_method(@mut self, method_type: &TypeMethod) {
        self.simple_visitor.visit_ty_method(method_type);
        walk_ty_method(self as @mut Visitor, method_type)
    }
    fn visit_trait_method(@mut self, trait_method: &trait_method) {
        self.simple_visitor.visit_trait_method(trait_method);
        walk_trait_method(self as @mut Visitor, trait_method)
    }
    fn visit_struct_def(@mut self,
                        struct_definition: @struct_def,
                        identifier: ident,
                        generics: &Generics,
                        node_id: NodeId) {
        self.simple_visitor.visit_struct_def(struct_definition,
                                             identifier,
                                             generics,
                                             node_id);
        walk_struct_def(self as @mut Visitor,
                         struct_definition,
                         identifier,
                         generics,
                         node_id)
    }
    fn visit_struct_field(@mut self, struct_field: @struct_field) {
        self.simple_visitor.visit_struct_field(struct_field);
        walk_struct_field(self as @mut Visitor, struct_field)
    }
}

