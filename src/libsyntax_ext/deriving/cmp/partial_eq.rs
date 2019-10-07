use crate::deriving::{path_local, path_std};
use crate::deriving::generic::*;
use crate::deriving::generic::ty::*;

use syntax::ast::{self, BinOpKind, Expr, ItemKind, MetaItem};
use syntax::ext::base::{Annotatable, ExtCtxt, SpecialDerives};
use syntax::ptr::P;
use syntax::symbol::sym;
use syntax_pos::{self, Span};

pub fn expand_deriving_partial_eq(cx: &mut ExtCtxt<'_>,
                                  span: Span,
                                  mitem: &MetaItem,
                                  item: &Annotatable,
                                  push: &mut dyn FnMut(Annotatable)) {
    cx.resolver.add_derives(cx.current_expansion.id.expn_data().parent, SpecialDerives::PARTIAL_EQ);

    // structures are equal if all fields are equal, and non equal, if
    // any fields are not equal or if the enum variants are different
    fn cs_op(cx: &mut ExtCtxt<'_>,
             span: Span,
             substr: &Substructure<'_>,
             op: BinOpKind,
             combiner: BinOpKind,
             base: bool)
             -> P<Expr>
    {
        let op = |cx: &mut ExtCtxt<'_>, span: Span, self_f: P<Expr>, other_fs: &[P<Expr>]| {
            let other_f = match other_fs {
                [o_f] => o_f,
                _ => cx.span_bug(span, "not exactly 2 arguments in `derive(PartialEq)`"),
            };

            cx.expr_binary(span, op, self_f, other_f.clone())
        };

        cs_fold1(true, // use foldl
            |cx, span, subexpr, self_f, other_fs| {
                let eq = op(cx, span, self_f, other_fs);
                cx.expr_binary(span, combiner, subexpr, eq)
            },
            |cx, args| {
                match args {
                    Some((span, self_f, other_fs)) => {
                        // Special-case the base case to generate cleaner code.
                        op(cx, span, self_f, other_fs)
                    }
                    None => cx.expr_bool(span, base),
                }
            },
            Box::new(|cx, span, _, _| cx.expr_bool(span, !base)),
            cx,
            span,
            substr)
    }

    fn cs_eq(cx: &mut ExtCtxt<'_>, span: Span, substr: &Substructure<'_>) -> P<Expr> {
        cs_op(cx, span, substr, BinOpKind::Eq, BinOpKind::And, true)
    }
    fn cs_ne(cx: &mut ExtCtxt<'_>, span: Span, substr: &Substructure<'_>) -> P<Expr> {
        cs_op(cx, span, substr, BinOpKind::Ne, BinOpKind::Or, false)
    }

    macro_rules! md {
        ($name:expr, $f:ident) => { {
            let inline = cx.meta_word(span, sym::inline);
            let attrs = vec![cx.attribute(inline)];
            MethodDef {
                name: $name,
                generics: LifetimeBounds::empty(),
                explicit_self: borrowed_explicit_self(),
                args: vec![(borrowed_self(), "other")],
                ret_ty: Literal(path_local!(bool)),
                attributes: attrs,
                is_unsafe: false,
                unify_fieldless_variants: true,
                combine_substructure: combine_substructure(Box::new(|a, b, c| {
                    $f(a, b, c)
                }))
            }
        } }
    }

    inject_impl_of_structural_trait(cx, span, item, push);

    // avoid defining `ne` if we can
    // c-like enums, enums without any fields and structs without fields
    // can safely define only `eq`.
    let mut methods = vec![md!("eq", cs_eq)];
    if !is_type_without_fields(item) {
        methods.push(md!("ne", cs_ne));
    }

    let trait_def = TraitDef {
        span,
        attributes: Vec::new(),
        path: path_std!(cx, cmp::PartialEq),
        additional_bounds: Vec::new(),
        generics: LifetimeBounds::empty(),
        is_unsafe: false,
        supports_unions: false,
        methods,
        associated_types: Vec::new(),
    };
    trait_def.expand(cx, mitem, item, push)
}

// Injects `impl<...> Structural for ItemType<...> { }`. In particular,
// does *not* add `where T: Structural` for parameters `T` in `...`.
// (That's the main reason we cannot use TraitDef here.)
fn inject_impl_of_structural_trait(cx: &mut ExtCtxt<'_>,
                                   span: Span,
                                   item: &Annotatable,
                                   push: &mut dyn FnMut(Annotatable)) {

    // set the expn ID so we can use the unstable trait.
    let span = span.fresh_expansion(syntax_pos::ExpnData::allow_unstable(
        syntax_pos::ExpnKind::Macro(syntax_pos::MacroKind::Derive, sym::PartialEq),
        span,
        cx.parse_sess.edition,
        [sym::structural_match][..].into()));

    let item = match *item {
        Annotatable::Item(ref item) => item,
        _ => {
            // Non-Item derive is an error, but it should have been
            // set earlier; see
            // libsyntax/ext/expand.rs:MacroExpander::expand()
            return;
        }
    };

    let generics = match item.kind {
        ItemKind::Struct(_, ref generics) => generics,
        ItemKind::Enum(_, ref generics) => generics,
        // Do not inject `impl Structural for Union`. (`PartialEq` does not
        // support unions, so we will see error downstream.)
        ItemKind::Union(..) => return,
        _ => unreachable!(),
    };

    // Create generics param list for where clauses and impl headers
    let mut generics = generics.clone();

    // Create the type of `self`.
    //
    // in addition, remove defaults from type params (impls cannot have them).
    let self_params: Vec<_> = generics.params.iter_mut().map(|param| match &mut param.kind {
        ast::GenericParamKind::Lifetime => {
            ast::GenericArg::Lifetime(cx.lifetime(span, param.ident))
        }
        ast::GenericParamKind::Type { default } => {
            *default = None;
            ast::GenericArg::Type(cx.ty_ident(span, param.ident))
        }
        ast::GenericParamKind::Const { ty: _ } => {
            ast::GenericArg::Const(cx.const_ident(span, param.ident))
        }
    }).collect();

    let type_ident = item.ident;

    let structural_path = path_std!(cx, marker::Structural);
    let trait_ref = cx.trait_ref(structural_path.to_path(cx, span, type_ident, &generics));
    let self_type = cx.ty_path(cx.path_all(span, false, vec![type_ident], self_params));

    // It would be nice to also encode constraint `where Self: Eq` (by adding it
    // onto `generics` cloned above). Unfortunately, that strategy runs afoul of
    // rust-lang/rust#48214. So we perform that additional check in the compiler
    // itself, instead of encoding it here.

    // Keep the lint and stability attributes of the original item, to control
    // how the generated implementation is linted.
    let mut attrs = Vec::new();
    attrs.extend(item.attrs
                 .iter()
                 .filter(|a| {
                     [sym::allow, sym::warn, sym::deny, sym::forbid, sym::stable, sym::unstable]
                         .contains(&a.name_or_empty())
                 })
                 .cloned());

    let newitem = cx.item(span,
                          ast::Ident::invalid(),
                          attrs,
                          ItemKind::Impl(ast::Unsafety::Normal,
                                         ast::ImplPolarity::Positive,
                                         ast::Defaultness::Final,
                                         generics,
                                         Some(trait_ref),
                                         self_type,
                                         Vec::new()));

    push(Annotatable::Item(newitem));
}
