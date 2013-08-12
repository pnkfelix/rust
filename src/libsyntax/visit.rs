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

pub trait Visitor<E:Clone> {
    // Main visit methods: the hooks you are meant to override
    // (remembering to put back in calls to walk_* as appropriate).

    fn visit_mod(@mut self, a:&_mod, _b:span, _c:NodeId, env:E) {
        self.walk_mod(a, env);
    }
    fn visit_view_item(@mut self, a:&view_item, env:E) {
        self.walk_view_item(a, env);
    }
    fn visit_foreign_item(@mut self, a:@foreign_item, env:E) {
        self.walk_foreign_item(a, env);
    }
    fn visit_item(@mut self, a:@item, env:E) {
        self.walk_item(a, env);
    }
    fn visit_local(@mut self, a:@Local, env:E) {
        self.walk_local(a, env);
    }
    fn visit_block(@mut self, a:&Block, env:E) {
        self.walk_block(a, env);
    }
    fn visit_stmt(@mut self, a:@stmt, env:E) {
        self.walk_stmt(a, env);
    }
    fn visit_arm(@mut self, a:&arm, env:E) {
        self.walk_arm(a, env);
    }
    fn visit_pat(@mut self, a:@pat, env:E) {
        self.walk_pat(a, env);
    }
    fn visit_decl(@mut self, a:@decl, env:E) {
        self.walk_decl(a, env);
    }
    fn visit_expr(@mut self, a:@expr, env:E) {
        self.walk_expr(a, env);
    }
    fn visit_expr_post(@mut self, _a:@expr, _env:E) {
        // no-op by default
    }
    fn visit_ty(@mut self, a:&Ty, env:E) {
        self.skip_ty(a, env);
    }
    fn visit_generics(@mut self, a:&Generics, env:E) {
        self.walk_generics(a, env);
    }
    fn visit_fn(@mut self, a:&fn_kind, b:&fn_decl, c:&Block, d:span, e:NodeId, env:E) {
        self.walk_fn(a, b, c, d, e, env);
    }
    fn visit_ty_method(@mut self, a:&TypeMethod, env:E) {
        self.walk_ty_method(a, env);
    }
    fn visit_trait_method(@mut self, a:&trait_method, env:E) {
        self.walk_trait_method(a, env);
    }
    fn visit_struct_def(@mut self, a:@struct_def, b:ident, c:&Generics, d:NodeId, env:E) {
        self.walk_struct_def(a, b, c, d, env);
    }
    fn visit_struct_field(@mut self, a:@struct_field, env:E) {
        self.walk_struct_field(a, env);
    }


    // helper methods to do recursive traversal
    pub fn walk_crate(@mut self, crate: &Crate, env: E) {
        self.visit_mod(&crate.module, crate.span, CRATE_NODE_ID, env)
    }

    pub fn walk_mod(@mut self, module: &_mod, env: E) {
        for view_item in module.view_items.iter() {
            self.visit_view_item(view_item, env.clone())
        }
        for item in module.items.iter() {
            self.visit_item(*item, env.clone())
        }
    }

    pub fn walk_view_item(@mut self, _i: &view_item, _env: E) {
        // Empty!
    }

    pub fn walk_local(@mut self, local: &Local, env: E) {
        self.visit_pat(local.pat, env.clone());
        self.visit_ty(&local.ty, env.clone());
        match local.init {
            None => {}
            Some(initializer) => self.visit_expr(initializer, env),
        }
    }

    fn walk_trait_ref(@mut self,
                       trait_ref: &ast::trait_ref,
                       env: E) {
        self.walk_path(&trait_ref.path, env)
    }

    pub fn walk_item(@mut self, item: &item, env: E) {
        match item.node {
            item_static(ref typ, _, expr) => {
                self.visit_ty(typ, env.clone());
                self.visit_expr(expr, env);
            }
            item_fn(ref declaration, purity, abi, ref generics, ref body) => {
                self.visit_fn(&fk_item_fn(item.ident, generics, purity, abi),
                              declaration,
                              body,
                              item.span,
                              item.id,
                              env)
            }
            item_mod(ref module) => {
                self.visit_mod(module, item.span, item.id, env)
            }
            item_foreign_mod(ref foreign_module) => {
                for view_item in foreign_module.view_items.iter() {
                    self.visit_view_item(view_item, env.clone())
                }
                for foreign_item in foreign_module.items.iter() {
                    self.visit_foreign_item(*foreign_item, env.clone())
                }
            }
            item_ty(ref typ, ref type_parameters) => {
                self.visit_ty(typ, env.clone());
                self.visit_generics(type_parameters, env)
            }
            item_enum(ref enum_definition, ref type_parameters) => {
                self.visit_generics(type_parameters, env.clone());
                self.walk_enum_def(enum_definition, type_parameters, env)
            }
            item_impl(ref type_parameters,
                      ref trait_references,
                      ref typ,
                      ref methods) => {
                self.visit_generics(type_parameters, env.clone());
                for trait_reference in trait_references.iter() {
                    self.walk_trait_ref(trait_reference, env.clone())
                }
                self.visit_ty(typ, env.clone());
                for method in methods.iter() {
                    self.walk_method_helper(*method, env.clone())
                }
            }
            item_struct(struct_definition, ref generics) => {
                self.visit_generics(generics, env.clone());
                self.visit_struct_def(struct_definition,
                                      item.ident,
                                      generics,
                                      item.id,
                                      env)
            }
            item_trait(ref generics, ref trait_paths, ref methods) => {
                self.visit_generics(generics, env.clone());
                for trait_path in trait_paths.iter() {
                    self.walk_path(&trait_path.path, env.clone())
                }
                for method in methods.iter() {
                    self.visit_trait_method(method, env.clone())
                }
            }
            item_mac(ref macro) => self.walk_mac(macro, env),
        }
    }

    pub fn walk_enum_def(@mut self,
                         enum_definition: &ast::enum_def,
                         generics: &Generics,
                         env: E) {
        for variant in enum_definition.variants.iter() {
            match variant.node.kind {
                tuple_variant_kind(ref variant_arguments) => {
                    for variant_argument in variant_arguments.iter() {
                        self.visit_ty(&variant_argument.ty, env.clone())
                    }
                }
                struct_variant_kind(struct_definition) => {
                    self.visit_struct_def(struct_definition,
                                          variant.node.name,
                                          generics,
                                          variant.node.id,
                                          env.clone())
                }
            }
        }
    }

    pub fn skip_ty(@mut self, _t: &Ty, _env: E) {
        // Empty!
    }

    pub fn walk_ty(@mut self, typ: &Ty, env: E) {
        match typ.node {
            ty_box(ref mutable_type) | ty_uniq(ref mutable_type) |
            ty_vec(ref mutable_type) | ty_ptr(ref mutable_type) |
            ty_rptr(_, ref mutable_type) => {
                self.visit_ty(mutable_type.ty, env)
            }
            ty_tup(ref tuple_element_types) => {
                for tuple_element_type in tuple_element_types.iter() {
                    self.visit_ty(tuple_element_type, env.clone())
                }
            }
            ty_closure(ref function_declaration) => {
                for argument in function_declaration.decl.inputs.iter() {
                    self.visit_ty(&argument.ty, env.clone())
                }
                self.visit_ty(&function_declaration.decl.output, env.clone());
                for bounds in function_declaration.bounds.iter() {
                    self.walk_ty_param_bounds(bounds, env.clone())
                }
            }
            ty_bare_fn(ref function_declaration) => {
                for argument in function_declaration.decl.inputs.iter() {
                    self.visit_ty(&argument.ty, env.clone())
                }
                self.visit_ty(&function_declaration.decl.output, env.clone())
            }
            ty_path(ref path, ref bounds, _) => {
                self.walk_path(path, env.clone());
                for bounds in bounds.iter() {
                    self.walk_ty_param_bounds(bounds, env.clone())
                }
            }
            ty_fixed_length_vec(ref mutable_type, expression) => {
                self.visit_ty(mutable_type.ty, env.clone());
                self.visit_expr(expression, env)
            }
            ty_nil | ty_bot | ty_mac(_) | ty_infer => ()
        }
    }

    pub fn walk_path(@mut self, path: &Path, env: E) {
        for typ in path.types.iter() {
            self.visit_ty(typ, env.clone())
        }
    }

    pub fn walk_pat(@mut self, pattern: &pat, env: E) {
        match pattern.node {
            pat_enum(ref path, ref children) => {
                self.walk_path(path, env.clone());
                for children in children.iter() {
                    for child in children.iter() {
                        self.visit_pat(*child, env.clone())
                    }
                }
            }
            pat_struct(ref path, ref fields, _) => {
                self.walk_path(path, env.clone());
                for field in fields.iter() {
                    self.visit_pat(field.pat, env.clone())
                }
            }
            pat_tup(ref tuple_elements) => {
                for tuple_element in tuple_elements.iter() {
                    self.visit_pat(*tuple_element, env.clone())
                }
            }
            pat_box(subpattern) |
            pat_uniq(subpattern) |
            pat_region(subpattern) => {
                self.visit_pat(subpattern, env)
            }
            pat_ident(_, ref path, ref optional_subpattern) => {
                self.walk_path(path, env.clone());
                match *optional_subpattern {
                    None => {}
                    Some(subpattern) => self.visit_pat(subpattern, env),
                }
            }
            pat_lit(expression) => self.visit_expr(expression, env),
            pat_range(lower_bound, upper_bound) => {
                self.visit_expr(lower_bound, env.clone());
                self.visit_expr(upper_bound, env)
            }
            pat_wild => (),
            pat_vec(ref prepattern, ref slice_pattern, ref postpatterns) => {
                for prepattern in prepattern.iter() {
                    self.visit_pat(*prepattern, env.clone())
                }
                for slice_pattern in slice_pattern.iter() {
                    self.visit_pat(*slice_pattern, env.clone())
                }
                for postpattern in postpatterns.iter() {
                    self.visit_pat(*postpattern, env.clone())
                }
            }
        }
    }

    pub fn walk_foreign_item(@mut self,
                             foreign_item: &foreign_item,
                             env: E) {
        match foreign_item.node {
            foreign_item_fn(ref function_declaration, ref generics) => {
                self.walk_fn_decl(function_declaration, env.clone());
                self.visit_generics(generics, env)
            }
            foreign_item_static(ref typ, _) => self.visit_ty(typ, env),
        }
    }

    pub fn walk_ty_param_bounds(@mut self,
                                bounds: &OptVec<TyParamBound>,
                                env: E) {
        for bound in bounds.iter() {
            match *bound {
                TraitTyParamBound(ref typ) => {
                    self.walk_trait_ref(typ, env.clone())
                }
                RegionTyParamBound => {}
            }
        }
    }

    pub fn walk_generics(@mut self,
                         generics: &Generics,
                         env: E) {
        for type_parameter in generics.ty_params.iter() {
            self.walk_ty_param_bounds(&type_parameter.bounds, env.clone())
        }
    }

    pub fn walk_fn_decl(@mut self,
                        function_declaration: &fn_decl,
                        env: E) {
        for argument in function_declaration.inputs.iter() {
            self.visit_pat(argument.pat, env.clone());
            self.visit_ty(&argument.ty, env.clone())
        }
        self.visit_ty(&function_declaration.output, env)
    }

    // Note: there is no visit_method() method in the visitor, instead override
    // visit_fn() and check for fk_method().  I named this visit_method_helper()
    // because it is not a default impl of any method, though I doubt that really
    // clarifies anything. - Niko
    pub fn walk_method_helper(@mut self,
                              method: &method,
                              env: E) {
        self.visit_fn(&fk_method(method.ident, &method.generics, method),
                      &method.decl,
                      &method.body,
                      method.span,
                      method.id,
                      env)
    }

    pub fn walk_fn(@mut self,
                   function_kind: &fn_kind,
                   function_declaration: &fn_decl,
                   function_body: &Block,
                   _s: span,
                   _n: NodeId,
                   env: E) {
        self.walk_fn_decl(function_declaration, env.clone());
        let generics = generics_of_fn(function_kind);
        self.visit_generics(&generics, env.clone());
        self.visit_block(function_body, env)
    }

    pub fn walk_ty_method(@mut self,
                          method_type: &TypeMethod,
                          env: E) {
        for argument_type in method_type.decl.inputs.iter() {
            self.visit_ty(&argument_type.ty, env.clone())
        }
        self.visit_generics(&method_type.generics, env.clone());
        self.visit_ty(&method_type.decl.output, env.clone())
    }

    pub fn walk_trait_method(@mut self,
                             trait_method: &trait_method,
                             env: E) {
        match *trait_method {
            required(ref method_type) => {
                self.visit_ty_method(method_type, env)
            }
            provided(method) => self.walk_method_helper(method, env),
        }
    }

    pub fn walk_struct_def(@mut self,
                           struct_definition: @struct_def,
                           _i: ast::ident,
                           _g: &Generics,
                           _n: NodeId,
                           env: E) {
        for field in struct_definition.fields.iter() {
            self.visit_struct_field(*field, env.clone())
        }
    }

    pub fn walk_struct_field(@mut self,
                             struct_field: &struct_field,
                             env: E) {
        self.visit_ty(&struct_field.node.ty, env)
    }

    pub fn walk_block(@mut self, block: &Block, env: E) {
        for view_item in block.view_items.iter() {
            self.visit_view_item(view_item, env.clone())
        }
        for statement in block.stmts.iter() {
            self.visit_stmt(*statement, env.clone())
        }
        self.walk_expr_opt(block.expr, env)
    }

    pub fn walk_stmt(@mut self, statement: &stmt, env: E) {
        match statement.node {
            stmt_decl(declaration, _) => self.visit_decl(declaration, env),
            stmt_expr(expression, _) | stmt_semi(expression, _) => {
                self.visit_expr(expression, env)
            }
            stmt_mac(ref macro, _) => self.walk_mac(macro, env),
        }
    }

    pub fn walk_decl(@mut self, declaration: &decl, env: E) {
        match declaration.node {
            decl_local(ref local) => self.visit_local(*local, env),
            decl_item(item) => self.visit_item(item, env),
        }
    }

    pub fn walk_expr_opt(@mut self,
                            optional_expression: Option<@expr>,
                            env: E) {
        match optional_expression {
            None => {}
            Some(expression) => self.visit_expr(expression, env),
        }
    }

    pub fn walk_exprs(@mut self,
                       expressions: &[@expr],
                       env: E) {
        for expression in expressions.iter() {
            self.visit_expr(*expression, env.clone())
        }
    }

    pub fn walk_mac(@mut self, _m: &mac, _env: E) {
        // Empty!
    }

    pub fn walk_expr(@mut self, expression: @expr, env: E) {
        match expression.node {
            expr_vstore(subexpression, _) => {
                self.visit_expr(subexpression, env.clone())
            }
            expr_vec(ref subexpressions, _) => {
                self.walk_exprs(*subexpressions, env.clone())
            }
            expr_repeat(element, count, _) => {
                self.visit_expr(element, env.clone());
                self.visit_expr(count, env.clone())
            }
            expr_struct(ref path, ref fields, optional_base) => {
                self.walk_path(path, env.clone());
                for field in fields.iter() {
                    self.visit_expr(field.expr, env.clone())
                }
                self.walk_expr_opt(optional_base, env.clone())
            }
            expr_tup(ref subexpressions) => {
                for subexpression in subexpressions.iter() {
                    self.visit_expr(*subexpression, env.clone())
                }
            }
            expr_call(callee_expression, ref arguments, _) => {
                for argument in arguments.iter() {
                    self.visit_expr(*argument, env.clone())
                }
                self.visit_expr(callee_expression, env.clone())
            }
            expr_method_call(_, callee, _, ref types, ref arguments, _) => {
                self.walk_exprs(*arguments, env.clone());
                for typ in types.iter() {
                    self.visit_ty(typ, env.clone())
                }
                self.visit_expr(callee, env.clone())
            }
            expr_binary(_, _, left_expression, right_expression) => {
                self.visit_expr(left_expression, env.clone());
                self.visit_expr(right_expression, env.clone())
            }
            expr_addr_of(_, subexpression) |
            expr_unary(_, _, subexpression) |
            expr_do_body(subexpression) => {
                self.visit_expr(subexpression, env.clone())
            }
            expr_lit(_) => {}
            expr_cast(subexpression, ref typ) => {
                self.visit_expr(subexpression, env.clone());
                self.visit_ty(typ, env.clone())
            }
            expr_if(head_expression, ref if_block, optional_else) => {
                self.visit_expr(head_expression, env.clone());
                self.visit_block(if_block, env.clone());
                self.walk_expr_opt(optional_else, env.clone())
            }
            expr_while(subexpression, ref block) => {
                self.visit_expr(subexpression, env.clone());
                self.visit_block(block, env.clone())
            }
            expr_for_loop(pattern, subexpression, ref block) => {
                self.visit_pat(pattern, env.clone());
                self.visit_expr(subexpression, env.clone());
                self.visit_block(block, env.clone())
            }
            expr_loop(ref block, _) => self.visit_block(block, env.clone()),
            expr_match(subexpression, ref arms) => {
                self.visit_expr(subexpression, env.clone());
                for arm in arms.iter() {
                    self.visit_arm(arm, env.clone())
                }
            }
            expr_fn_block(ref function_declaration, ref body) => {
                self.visit_fn(&fk_fn_block,
                              function_declaration,
                              body,
                              expression.span,
                              expression.id,
                              env.clone())
            }
            expr_block(ref block) => self.visit_block(block, env.clone()),
            expr_assign(left_hand_expression, right_hand_expression) => {
                self.visit_expr(right_hand_expression, env.clone());
                self.visit_expr(left_hand_expression, env.clone())
            }
            expr_assign_op(_, _, left_expression, right_expression) => {
                self.visit_expr(right_expression, env.clone());
                self.visit_expr(left_expression, env.clone())
            }
            expr_field(subexpression, _, ref types) => {
                self.visit_expr(subexpression, env.clone());
                for typ in types.iter() {
                    self.visit_ty(typ, env.clone())
                }
            }
            expr_index(_, main_expression, index_expression) => {
                self.visit_expr(main_expression, env.clone());
                self.visit_expr(index_expression, env.clone())
            }
            expr_path(ref path) => self.walk_path(path, env.clone()),
            expr_self | expr_break(_) | expr_again(_) => {}
            expr_ret(optional_expression) => {
                self.walk_expr_opt(optional_expression, env.clone())
            }
            expr_log(level, subexpression) => {
                self.visit_expr(level, env.clone());
                self.visit_expr(subexpression, env.clone());
            }
            expr_mac(ref macro) => self.walk_mac(macro, env.clone()),
            expr_paren(subexpression) => {
                self.visit_expr(subexpression, env.clone())
            }
            expr_inline_asm(ref assembler) => {
                for &(_, input) in assembler.inputs.iter() {
                    self.visit_expr(input, env.clone())
                }
                for &(_, output) in assembler.outputs.iter() {
                    self.visit_expr(output, env.clone())
                }
            }
        }

        self.visit_expr_post(expression, env.clone())
    }

    pub fn walk_arm(@mut self, arm: &arm, env: E) {
        for pattern in arm.pats.iter() {
            self.visit_pat(*pattern, env.clone())
        }
        self.walk_expr_opt(arm.guard, env.clone());
        self.visit_block(&arm.body, env)
    }
}

pub fn visit_crate<E:Clone>(visitor: @mut Visitor<E>, crate: &Crate, env: E) {
    visitor.walk_crate(crate, env);
}

pub fn visit_mod<E:Clone>(visitor: @mut Visitor<E>, module: &_mod, env: E) {
    visitor.walk_mod(module, env);
}

pub fn visit_view_item<E:Clone>(visitor: @mut Visitor<E>, i: &view_item, env: E) {
    visitor.walk_view_item(i, env);
}

pub fn visit_local<E:Clone>(visitor: @mut Visitor<E>, local: &Local, env: E) {
    visitor.walk_local(local, env);
}

fn visit_trait_ref<E:Clone>(visitor: @mut Visitor<E>,
                            trait_ref: &ast::trait_ref,
                            env: E) {
    visitor.walk_trait_ref(trait_ref, env);
}

pub fn visit_item<E:Clone>(visitor: @mut Visitor<E>, item: &item, env: E) {
    visitor.walk_item(item, env);
}

pub fn visit_enum_def<E:Clone>(visitor: @mut Visitor<E>,
                               enum_definition: &ast::enum_def,
                               generics: &Generics,
                               env: E) {
    visitor.walk_enum_def(enum_definition, generics, env);
}

pub fn skip_ty<E:Clone>(visitor: @mut Visitor<E>, typ: &Ty, env: E) {
    visitor.skip_ty(typ, env);
}

pub fn visit_ty<E:Clone>(visitor: @mut Visitor<E>, typ: &Ty, env: E) {
    visitor.walk_ty(typ, env);
}

pub fn visit_path<E:Clone>(visitor: @mut Visitor<E>, path: &Path, env: E) {
    visitor.walk_path(path, env);
}

pub fn visit_pat<E:Clone>(visitor: @mut Visitor<E>, pattern: &pat, env: E) {
    visitor.walk_pat(pattern, env);
}

pub fn visit_foreign_item<E:Clone>(visitor: @mut Visitor<E>,
                                   foreign_item: &foreign_item,
                                   env: E) {
    visitor.walk_foreign_item(foreign_item, env);
}

pub fn visit_ty_param_bounds<E:Clone>(visitor: @mut Visitor<E>,
                                      bounds: &OptVec<TyParamBound>,
                                      env: E) {
    visitor.walk_ty_param_bounds(bounds, env);
}

pub fn visit_generics<E:Clone>(visitor: @mut Visitor<E>,
                               generics: &Generics,
                               env: E) {
    visitor.walk_generics(generics, env);
}

pub fn visit_fn_decl<E:Clone>(visitor: @mut Visitor<E>,
                              function_declaration: &fn_decl,
                              env: E) {
    visitor.walk_fn_decl(function_declaration, env);
}

// Note: there is no visit_method() method in the visitor, instead override
// visit_fn() and check for fk_method().  I named this visit_method_helper()
// because it is not a default impl of any method, though I doubt that really
// clarifies anything. - Niko
pub fn visit_method_helper<E:Clone>(visitor: @mut Visitor<E>,
                                    method: &method,
                                    env: E) {
    visitor.walk_method_helper(method, env);
}

pub fn visit_fn<E:Clone>(visitor: @mut Visitor<E>,
                         function_kind: &fn_kind,
                         function_declaration: &fn_decl,
                         function_body: &Block,
                         s: span,
                         n: NodeId,
                         env: E) {
    visitor.walk_fn(function_kind,
                    function_declaration,
                    function_body,
                    s,
                    n,
                    env);
}

pub fn visit_ty_method<E:Clone>(visitor: @mut Visitor<E>,
                                method_type: &TypeMethod,
                                env: E) {
    visitor.walk_ty_method(method_type, env);
}

pub fn visit_trait_method<E:Clone>(visitor: @mut Visitor<E>,
                                   trait_method: &trait_method,
                                   env: E) {
    visitor.walk_trait_method(trait_method, env);
}

pub fn visit_struct_def<E:Clone>(visitor: @mut Visitor<E>,
                                 struct_definition: @struct_def,
                                 i: ast::ident,
                                 g: &Generics,
                                 n: NodeId,
                                 env: E) {
    visitor.walk_struct_def(struct_definition, i, g, n, env);
}

pub fn visit_struct_field<E:Clone>(visitor: @mut Visitor<E>,
                                   struct_field: &struct_field,
                                   env: E) {
    visitor.walk_struct_field(struct_field, env);
}

pub fn visit_block<E:Clone>(visitor: @mut Visitor<E>, block: &Block, env: E) {
    visitor.walk_block(block, env);
}

pub fn visit_stmt<E:Clone>(visitor: @mut Visitor<E>, statement: &stmt, env: E) {
    visitor.walk_stmt(statement, env);
}

pub fn visit_decl<E:Clone>(visitor: @mut Visitor<E>, declaration: &decl, env: E) {
    visitor.walk_decl(declaration, env);
}

pub fn visit_expr_opt<E:Clone>(visitor: @mut Visitor<E>,
                         optional_expression: Option<@expr>,
                         env: E) {
    visitor.walk_expr_opt(optional_expression, env);
}

pub fn visit_exprs<E:Clone>(visitor: @mut Visitor<E>,
                            expressions: &[@expr],
                            env: E) {
    visitor.walk_exprs(expressions, env);
}

pub fn visit_mac<E:Clone>(visitor: @mut Visitor<E>, m: &mac, env: E) {
    visitor.walk_mac(m, env);
}

pub fn visit_expr<E:Clone>(visitor: @mut Visitor<E>, expression: @expr, env: E) {
    visitor.walk_expr(expression, env);
}

pub fn visit_arm<E:Clone>(visitor: @mut Visitor<E>, arm: &arm, env: E) {
    visitor.walk_arm(arm, env);
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
    simple_visitor: @mut SimpleVisitor,
}

impl Visitor<()> for SimpleVisitorVisitor {
    fn visit_mod(@mut self,
                 module: &_mod,
                 span: span,
                 node_id: NodeId,
                 env: ()) {
        self.simple_visitor.visit_mod(module, span, node_id);
        visit_mod(self as @mut Visitor<()>, module, env)
    }
    fn visit_view_item(@mut self, view_item: &view_item, env: ()) {
        self.simple_visitor.visit_view_item(view_item);
        visit_view_item(self as @mut Visitor<()>, view_item, env)
    }
    fn visit_foreign_item(@mut self, foreign_item: @foreign_item, env: ()) {
        self.simple_visitor.visit_foreign_item(foreign_item);
        visit_foreign_item(self as @mut Visitor<()>, foreign_item, env)
    }
    fn visit_item(@mut self, item: @item, env: ()) {
        self.simple_visitor.visit_item(item);
        visit_item(self as @mut Visitor<()>, item, env)
    }
    fn visit_local(@mut self, local: @Local, env: ()) {
        self.simple_visitor.visit_local(local);
        visit_local(self as @mut Visitor<()>, local, env)
    }
    fn visit_block(@mut self, block: &Block, env: ()) {
        self.simple_visitor.visit_block(block);
        visit_block(self as @mut Visitor<()>, block, env)
    }
    fn visit_stmt(@mut self, statement: @stmt, env: ()) {
        self.simple_visitor.visit_stmt(statement);
        visit_stmt(self as @mut Visitor<()>, statement, env)
    }
    fn visit_arm(@mut self, arm: &arm, env: ()) {
        self.simple_visitor.visit_arm(arm);
        visit_arm(self as @mut Visitor<()>, arm, env)
    }
    fn visit_pat(@mut self, pattern: @pat, env: ()) {
        self.simple_visitor.visit_pat(pattern);
        visit_pat(self as @mut Visitor<()>, pattern, env)
    }
    fn visit_decl(@mut self, declaration: @decl, env: ()) {
        self.simple_visitor.visit_decl(declaration);
        visit_decl(self as @mut Visitor<()>, declaration, env)
    }
    fn visit_expr(@mut self, expression: @expr, env: ()) {
        self.simple_visitor.visit_expr(expression);
        visit_expr(self as @mut Visitor<()>, expression, env)
    }
    fn visit_expr_post(@mut self, expression: @expr, _: ()) {
        self.simple_visitor.visit_expr_post(expression)
    }
    fn visit_ty(@mut self, typ: &Ty, env: ()) {
        self.simple_visitor.visit_ty(typ);
        visit_ty(self as @mut Visitor<()>, typ, env)
    }
    fn visit_generics(@mut self, generics: &Generics, env: ()) {
        self.simple_visitor.visit_generics(generics);
        visit_generics(self as @mut Visitor<()>, generics, env)
    }
    fn visit_fn(@mut self,
                function_kind: &fn_kind,
                function_declaration: &fn_decl,
                block: &Block,
                span: span,
                node_id: NodeId,
                env: ()) {
        self.simple_visitor.visit_fn(function_kind,
                                     function_declaration,
                                     block,
                                     span,
                                     node_id);
        visit_fn(self as @mut Visitor<()>,
                 function_kind,
                 function_declaration,
                 block,
                 span,
                 node_id,
                 env)
    }
    fn visit_ty_method(@mut self, method_type: &TypeMethod, env: ()) {
        self.simple_visitor.visit_ty_method(method_type);
        visit_ty_method(self as @mut Visitor<()>, method_type, env)
    }
    fn visit_trait_method(@mut self, trait_method: &trait_method, env: ()) {
        self.simple_visitor.visit_trait_method(trait_method);
        visit_trait_method(self as @mut Visitor<()>, trait_method, env)
    }
    fn visit_struct_def(@mut self,
                        struct_definition: @struct_def,
                        identifier: ident,
                        generics: &Generics,
                        node_id: NodeId,
                        env: ()) {
        self.simple_visitor.visit_struct_def(struct_definition,
                                             identifier,
                                             generics,
                                             node_id);
        visit_struct_def(self as @mut Visitor<()>,
                         struct_definition,
                         identifier,
                         generics,
                         node_id,
                         env)
    }
    fn visit_struct_field(@mut self, struct_field: @struct_field, env: ()) {
        self.simple_visitor.visit_struct_field(struct_field);
        visit_struct_field(self as @mut Visitor<()>, struct_field, env)
    }
}

