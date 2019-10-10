//! Validation of patterns/matches.

mod _match;
mod check_match;

pub(crate) use self::check_match::check_match;

use crate::const_eval::const_variant_index;

use crate::hair::util::UserAnnotatedTyHelpers;
use crate::hair::constant::*;

use rustc::lint;
use rustc::infer::InferCtxt;
use rustc::mir::{Field, BorrowKind, Mutability};
use rustc::mir::{UserTypeProjection};
use rustc::mir::interpret::{GlobalId, ConstValue, get_slice_bytes, sign_extend};
use rustc::traits::{self, ConstPatternStructural, TraitEngine};
use rustc::traits::{ObligationCause, PredicateObligation};
use rustc::ty::{self, Region, TyCtxt, AdtDef, Ty, UserType, DefIdTree, ToPredicate};
use rustc::ty::{CanonicalUserType, CanonicalUserTypeAnnotation, CanonicalUserTypeAnnotations};
use rustc::ty::subst::{SubstsRef, GenericArg};
use rustc::ty::layout::VariantIdx;
use rustc::hir::{self, RangeEnd};
use rustc::hir::def::{CtorOf, Res, DefKind, CtorKind};
use rustc::hir::pat_util::EnumerateAndAdjustIterator;
use rustc::hir::ptr::P;

use rustc_index::vec::Idx;
use rustc_data_structures::fx::FxHashSet;

use std::cmp::Ordering;
use std::fmt;
use syntax::ast;
use syntax::symbol::sym;
use syntax_pos::Span;

#[derive(Clone, Debug)]
pub enum PatternError {
    AssocConstInPattern(Span),
    StaticInPattern(Span),
    FloatBug,
    NonConstPath(Span),
}

#[derive(Copy, Clone, Debug)]
pub enum BindingMode {
    ByValue,
    ByRef(BorrowKind),
}

#[derive(Clone, Debug)]
pub struct FieldPat<'tcx> {
    pub field: Field,
    pub pattern: Pat<'tcx>,
}

#[derive(Clone, Debug)]
pub struct Pat<'tcx> {
    pub ty: Ty<'tcx>,
    pub span: Span,
    pub kind: Box<PatKind<'tcx>>,
}


#[derive(Copy, Clone, Debug, PartialEq)]
pub struct PatTyProj<'tcx> {
    pub user_ty: CanonicalUserType<'tcx>,
}

impl<'tcx> PatTyProj<'tcx> {
    pub(crate) fn from_user_type(user_annotation: CanonicalUserType<'tcx>) -> Self {
        Self {
            user_ty: user_annotation,
        }
    }

    pub(crate) fn user_ty(
        self,
        annotations: &mut CanonicalUserTypeAnnotations<'tcx>,
        inferred_ty: Ty<'tcx>,
        span: Span,
    ) -> UserTypeProjection {
        UserTypeProjection {
            base: annotations.push(CanonicalUserTypeAnnotation {
                span,
                user_ty: self.user_ty,
                inferred_ty,
            }),
            projs: Vec::new(),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Ascription<'tcx> {
    pub user_ty: PatTyProj<'tcx>,
    /// Variance to use when relating the type `user_ty` to the **type of the value being
    /// matched**. Typically, this is `Variance::Covariant`, since the value being matched must
    /// have a type that is some subtype of the ascribed type.
    ///
    /// Note that this variance does not apply for any bindings within subpatterns. The type
    /// assigned to those bindings must be exactly equal to the `user_ty` given here.
    ///
    /// The only place where this field is not `Covariant` is when matching constants, where
    /// we currently use `Contravariant` -- this is because the constant type just needs to
    /// be "comparable" to the type of the input value. So, for example:
    ///
    /// ```text
    /// match x { "foo" => .. }
    /// ```
    ///
    /// requires that `&'static str <: T_x`, where `T_x` is the type of `x`. Really, we should
    /// probably be checking for a `PartialEq` impl instead, but this preserves the behavior
    /// of the old type-check for now. See #57280 for details.
    pub variance: ty::Variance,
    pub user_ty_span: Span,
}

#[derive(Clone, Debug)]
pub enum PatKind<'tcx> {
    Wild,

    AscribeUserType {
        ascription: Ascription<'tcx>,
        subpattern: Pat<'tcx>,
    },

    /// `x`, `ref x`, `x @ P`, etc.
    Binding {
        mutability: Mutability,
        name: ast::Name,
        mode: BindingMode,
        var: hir::HirId,
        ty: Ty<'tcx>,
        subpattern: Option<Pat<'tcx>>,
    },

    /// `Foo(...)` or `Foo{...}` or `Foo`, where `Foo` is a variant name from an ADT with
    /// multiple variants.
    Variant {
        adt_def: &'tcx AdtDef,
        substs: SubstsRef<'tcx>,
        variant_index: VariantIdx,
        subpatterns: Vec<FieldPat<'tcx>>,
    },

    /// `(...)`, `Foo(...)`, `Foo{...}`, or `Foo`, where `Foo` is a variant name from an ADT with
    /// a single variant.
    Leaf {
        subpatterns: Vec<FieldPat<'tcx>>,
    },

    /// `box P`, `&P`, `&mut P`, etc.
    Deref {
        subpattern: Pat<'tcx>,
    },

    Constant {
        value: &'tcx ty::Const<'tcx>,
    },

    Range(PatRange<'tcx>),

    /// Matches against a slice, checking the length and extracting elements.
    /// irrefutable when there is a slice pattern and both `prefix` and `suffix` are empty.
    /// e.g., `&[ref xs @ ..]`.
    Slice {
        prefix: Vec<Pat<'tcx>>,
        slice: Option<Pat<'tcx>>,
        suffix: Vec<Pat<'tcx>>,
    },

    /// Fixed match against an array; irrefutable.
    Array {
        prefix: Vec<Pat<'tcx>>,
        slice: Option<Pat<'tcx>>,
        suffix: Vec<Pat<'tcx>>,
    },

    /// An or-pattern, e.g. `p | q`.
    /// Invariant: `pats.len() >= 2`.
    Or {
        pats: Vec<Pat<'tcx>>,
    },
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct PatRange<'tcx> {
    pub lo: &'tcx ty::Const<'tcx>,
    pub hi: &'tcx ty::Const<'tcx>,
    pub end: RangeEnd,
}

impl<'tcx> fmt::Display for Pat<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Printing lists is a chore.
        let mut first = true;
        let mut start_or_continue = |s| {
            if first {
                first = false;
                ""
            } else {
                s
            }
        };
        let mut start_or_comma = || start_or_continue(", ");

        match *self.kind {
            PatKind::Wild => write!(f, "_"),
            PatKind::AscribeUserType { ref subpattern, .. } =>
                write!(f, "{}: _", subpattern),
            PatKind::Binding { mutability, name, mode, ref subpattern, .. } => {
                let is_mut = match mode {
                    BindingMode::ByValue => mutability == Mutability::Mut,
                    BindingMode::ByRef(bk) => {
                        write!(f, "ref ")?;
                        match bk { BorrowKind::Mut { .. } => true, _ => false }
                    }
                };
                if is_mut {
                    write!(f, "mut ")?;
                }
                write!(f, "{}", name)?;
                if let Some(ref subpattern) = *subpattern {
                    write!(f, " @ {}", subpattern)?;
                }
                Ok(())
            }
            PatKind::Variant { ref subpatterns, .. } |
            PatKind::Leaf { ref subpatterns } => {
                let variant = match *self.kind {
                    PatKind::Variant { adt_def, variant_index, .. } => {
                        Some(&adt_def.variants[variant_index])
                    }
                    _ => if let ty::Adt(adt, _) = self.ty.kind {
                        if !adt.is_enum() {
                            Some(&adt.variants[VariantIdx::new(0)])
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                };

                if let Some(variant) = variant {
                    write!(f, "{}", variant.ident)?;

                    // Only for Adt we can have `S {...}`,
                    // which we handle separately here.
                    if variant.ctor_kind == CtorKind::Fictive {
                        write!(f, " {{ ")?;

                        let mut printed = 0;
                        for p in subpatterns {
                            if let PatKind::Wild = *p.pattern.kind {
                                continue;
                            }
                            let name = variant.fields[p.field.index()].ident;
                            write!(f, "{}{}: {}", start_or_comma(), name, p.pattern)?;
                            printed += 1;
                        }

                        if printed < variant.fields.len() {
                            write!(f, "{}..", start_or_comma())?;
                        }

                        return write!(f, " }}");
                    }
                }

                let num_fields = variant.map_or(subpatterns.len(), |v| v.fields.len());
                if num_fields != 0 || variant.is_none() {
                    write!(f, "(")?;
                    for i in 0..num_fields {
                        write!(f, "{}", start_or_comma())?;

                        // Common case: the field is where we expect it.
                        if let Some(p) = subpatterns.get(i) {
                            if p.field.index() == i {
                                write!(f, "{}", p.pattern)?;
                                continue;
                            }
                        }

                        // Otherwise, we have to go looking for it.
                        if let Some(p) = subpatterns.iter().find(|p| p.field.index() == i) {
                            write!(f, "{}", p.pattern)?;
                        } else {
                            write!(f, "_")?;
                        }
                    }
                    write!(f, ")")?;
                }

                Ok(())
            }
            PatKind::Deref { ref subpattern } => {
                match self.ty.kind {
                    ty::Adt(def, _) if def.is_box() => write!(f, "box ")?,
                    ty::Ref(_, _, mutbl) => {
                        write!(f, "&")?;
                        if mutbl == hir::MutMutable {
                            write!(f, "mut ")?;
                        }
                    }
                    _ => bug!("{} is a bad Deref pattern type", self.ty)
                }
                write!(f, "{}", subpattern)
            }
            PatKind::Constant { value } => {
                write!(f, "{}", value)
            }
            PatKind::Range(PatRange { lo, hi, end }) => {
                write!(f, "{}", lo)?;
                match end {
                    RangeEnd::Included => write!(f, "..=")?,
                    RangeEnd::Excluded => write!(f, "..")?,
                }
                write!(f, "{}", hi)
            }
            PatKind::Slice { ref prefix, ref slice, ref suffix } |
            PatKind::Array { ref prefix, ref slice, ref suffix } => {
                write!(f, "[")?;
                for p in prefix {
                    write!(f, "{}{}", start_or_comma(), p)?;
                }
                if let Some(ref slice) = *slice {
                    write!(f, "{}", start_or_comma())?;
                    match *slice.kind {
                        PatKind::Wild => {}
                        _ => write!(f, "{}", slice)?
                    }
                    write!(f, "..")?;
                }
                for p in suffix {
                    write!(f, "{}{}", start_or_comma(), p)?;
                }
                write!(f, "]")
            }
            PatKind::Or { ref pats } => {
                for pat in pats {
                    write!(f, "{}{}", start_or_continue(" | "), pat)?;
                }
                Ok(())
            }
        }
    }
}

pub struct PatCtxt<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub param_env: ty::ParamEnv<'tcx>,
    pub tables: &'a ty::TypeckTables<'tcx>,
    pub substs: SubstsRef<'tcx>,
    pub errors: Vec<PatternError>,
    include_lint_checks: bool,
}

impl<'a, 'tcx> Pat<'tcx> {
    pub fn from_hir(
        tcx: TyCtxt<'tcx>,
        param_env_and_substs: ty::ParamEnvAnd<'tcx, SubstsRef<'tcx>>,
        tables: &'a ty::TypeckTables<'tcx>,
        pat: &'tcx hir::Pat,
    ) -> Self {
        let mut pcx = PatCtxt::new(tcx, param_env_and_substs, tables);
        let result = pcx.lower_pattern(pat);
        if !pcx.errors.is_empty() {
            let msg = format!("encountered errors lowering pattern: {:?}", pcx.errors);
            tcx.sess.delay_span_bug(pat.span, &msg);
        }
        debug!("Pat::from_hir({:?}) = {:?}", pat, result);
        result
    }
}

impl<'a, 'tcx> PatCtxt<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        param_env_and_substs: ty::ParamEnvAnd<'tcx, SubstsRef<'tcx>>,
        tables: &'a ty::TypeckTables<'tcx>,
    ) -> Self {
        PatCtxt {
            tcx,
            param_env: param_env_and_substs.param_env,
            tables,
            substs: param_env_and_substs.value,
            errors: vec![],
            include_lint_checks: false,
        }
    }

    pub fn include_lint_checks(&mut self) -> &mut Self {
        self.include_lint_checks = true;
        self
    }

    pub fn lower_pattern(&mut self, pat: &'tcx hir::Pat) -> Pat<'tcx> {
        // When implicit dereferences have been inserted in this pattern, the unadjusted lowered
        // pattern has the type that results *after* dereferencing. For example, in this code:
        //
        // ```
        // match &&Some(0i32) {
        //     Some(n) => { ... },
        //     _ => { ... },
        // }
        // ```
        //
        // the type assigned to `Some(n)` in `unadjusted_pat` would be `Option<i32>` (this is
        // determined in rustc_typeck::check::match). The adjustments would be
        //
        // `vec![&&Option<i32>, &Option<i32>]`.
        //
        // Applying the adjustments, we want to instead output `&&Some(n)` (as a HAIR pattern). So
        // we wrap the unadjusted pattern in `PatKind::Deref` repeatedly, consuming the
        // adjustments in *reverse order* (last-in-first-out, so that the last `Deref` inserted
        // gets the least-dereferenced type).
        let unadjusted_pat = self.lower_pattern_unadjusted(pat);
        self.tables
            .pat_adjustments()
            .get(pat.hir_id)
            .unwrap_or(&vec![])
            .iter()
            .rev()
            .fold(unadjusted_pat, |pat, ref_ty| {
                    debug!("{:?}: wrapping pattern with type {:?}", pat, ref_ty);
                    Pat {
                        span: pat.span,
                        ty: ref_ty,
                        kind: Box::new(PatKind::Deref { subpattern: pat }),
                    }
                },
            )
    }

    fn lower_range_expr(
        &mut self,
        expr: &'tcx hir::Expr,
    ) -> (PatKind<'tcx>, Option<Ascription<'tcx>>) {
        match self.lower_lit(expr) {
            PatKind::AscribeUserType {
                ascription: lo_ascription,
                subpattern: Pat { kind: box kind, .. },
            } => (kind, Some(lo_ascription)),
            kind => (kind, None),
        }
    }

    fn lower_pattern_unadjusted(&mut self, pat: &'tcx hir::Pat) -> Pat<'tcx> {
        let mut ty = self.tables.node_type(pat.hir_id);

        let kind = match pat.kind {
            hir::PatKind::Wild => PatKind::Wild,

            hir::PatKind::Lit(ref value) => self.lower_lit(value),

            hir::PatKind::Range(ref lo_expr, ref hi_expr, end) => {
                let (lo, lo_ascription) = self.lower_range_expr(lo_expr);
                let (hi, hi_ascription) = self.lower_range_expr(hi_expr);

                let mut kind = match (lo, hi) {
                    (PatKind::Constant { value: lo }, PatKind::Constant { value: hi }) => {
                        assert_eq!(lo.ty, ty);
                        assert_eq!(hi.ty, ty);
                        let cmp = compare_const_vals(
                            self.tcx,
                            lo,
                            hi,
                            self.param_env,
                            ty,
                        );
                        match (end, cmp) {
                            (RangeEnd::Excluded, Some(Ordering::Less)) =>
                                PatKind::Range(PatRange { lo, hi, end }),
                            (RangeEnd::Excluded, _) => {
                                span_err!(
                                    self.tcx.sess,
                                    lo_expr.span,
                                    E0579,
                                    "lower range bound must be less than upper",
                                );
                                PatKind::Wild
                            }
                            (RangeEnd::Included, Some(Ordering::Equal)) => {
                                PatKind::Constant { value: lo }
                            }
                            (RangeEnd::Included, Some(Ordering::Less)) => {
                                PatKind::Range(PatRange { lo, hi, end })
                            }
                            (RangeEnd::Included, _) => {
                                let mut err = struct_span_err!(
                                    self.tcx.sess,
                                    lo_expr.span,
                                    E0030,
                                    "lower range bound must be less than or equal to upper"
                                );
                                err.span_label(
                                    lo_expr.span,
                                    "lower bound larger than upper bound",
                                );
                                if self.tcx.sess.teach(&err.get_code().unwrap()) {
                                    err.note("When matching against a range, the compiler \
                                              verifies that the range is non-empty. Range \
                                              patterns include both end-points, so this is \
                                              equivalent to requiring the start of the range \
                                              to be less than or equal to the end of the range.");
                                }
                                err.emit();
                                PatKind::Wild
                            }
                        }
                    },
                    ref pats => {
                        self.tcx.sess.delay_span_bug(
                            pat.span,
                            &format!(
                                "found bad range pattern `{:?}` outside of error recovery",
                                pats,
                            ),
                        );

                        PatKind::Wild
                    },
                };

                // If we are handling a range with associated constants (e.g.
                // `Foo::<'a>::A..=Foo::B`), we need to put the ascriptions for the associated
                // constants somewhere. Have them on the range pattern.
                for ascription in &[lo_ascription, hi_ascription] {
                    if let Some(ascription) = ascription {
                        kind = PatKind::AscribeUserType {
                            ascription: *ascription,
                            subpattern: Pat { span: pat.span, ty, kind: Box::new(kind), },
                        };
                    }
                }

                kind
            }

            hir::PatKind::Path(ref qpath) => {
                return self.lower_path(qpath, pat.hir_id, pat.span);
            }

            hir::PatKind::Ref(ref subpattern, _) |
            hir::PatKind::Box(ref subpattern) => {
                PatKind::Deref { subpattern: self.lower_pattern(subpattern) }
            }

            hir::PatKind::Slice(ref prefix, ref slice, ref suffix) => {
                match ty.kind {
                    ty::Ref(_, ty, _) =>
                        PatKind::Deref {
                            subpattern: Pat {
                                ty,
                                span: pat.span,
                                kind: Box::new(self.slice_or_array_pattern(
                                    pat.span, ty, prefix, slice, suffix))
                            },
                        },
                    ty::Slice(..) |
                    ty::Array(..) =>
                        self.slice_or_array_pattern(pat.span, ty, prefix, slice, suffix),
                    ty::Error => { // Avoid ICE
                        return Pat { span: pat.span, ty, kind: Box::new(PatKind::Wild) };
                    }
                    _ =>
                        span_bug!(
                            pat.span,
                            "unexpanded type for vector pattern: {:?}",
                            ty),
                }
            }

            hir::PatKind::Tuple(ref subpatterns, ddpos) => {
                match ty.kind {
                    ty::Tuple(ref tys) => {
                        let subpatterns =
                            subpatterns.iter()
                                       .enumerate_and_adjust(tys.len(), ddpos)
                                       .map(|(i, subpattern)| FieldPat {
                                            field: Field::new(i),
                                            pattern: self.lower_pattern(subpattern)
                                       })
                                       .collect();

                        PatKind::Leaf { subpatterns }
                    }
                    ty::Error => { // Avoid ICE (#50577)
                        return Pat { span: pat.span, ty, kind: Box::new(PatKind::Wild) };
                    }
                    _ => span_bug!(pat.span, "unexpected type for tuple pattern: {:?}", ty),
                }
            }

            hir::PatKind::Binding(_, id, ident, ref sub) => {
                let var_ty = self.tables.node_type(pat.hir_id);
                if let ty::Error = var_ty.kind {
                    // Avoid ICE
                    return Pat { span: pat.span, ty, kind: Box::new(PatKind::Wild) };
                };
                let bm = *self.tables.pat_binding_modes().get(pat.hir_id)
                                                         .expect("missing binding mode");
                let (mutability, mode) = match bm {
                    ty::BindByValue(hir::MutMutable) =>
                        (Mutability::Mut, BindingMode::ByValue),
                    ty::BindByValue(hir::MutImmutable) =>
                        (Mutability::Not, BindingMode::ByValue),
                    ty::BindByReference(hir::MutMutable) =>
                        (Mutability::Not, BindingMode::ByRef(
                            BorrowKind::Mut { allow_two_phase_borrow: false })),
                    ty::BindByReference(hir::MutImmutable) =>
                        (Mutability::Not, BindingMode::ByRef(
                            BorrowKind::Shared)),
                };

                // A ref x pattern is the same node used for x, and as such it has
                // x's type, which is &T, where we want T (the type being matched).
                if let ty::BindByReference(_) = bm {
                    if let ty::Ref(_, rty, _) = ty.kind {
                        ty = rty;
                    } else {
                        bug!("`ref {}` has wrong type {}", ident, ty);
                    }
                }

                PatKind::Binding {
                    mutability,
                    mode,
                    name: ident.name,
                    var: id,
                    ty: var_ty,
                    subpattern: self.lower_opt_pattern(sub),
                }
            }

            hir::PatKind::TupleStruct(ref qpath, ref subpatterns, ddpos) => {
                let res = self.tables.qpath_res(qpath, pat.hir_id);
                let adt_def = match ty.kind {
                    ty::Adt(adt_def, _) => adt_def,
                    ty::Error => { // Avoid ICE (#50585)
                        return Pat { span: pat.span, ty, kind: Box::new(PatKind::Wild) };
                    }
                    _ => span_bug!(pat.span,
                                   "tuple struct pattern not applied to an ADT {:?}",
                                   ty),
                };
                let variant_def = adt_def.variant_of_res(res);

                let subpatterns =
                        subpatterns.iter()
                                   .enumerate_and_adjust(variant_def.fields.len(), ddpos)
                                   .map(|(i, field)| FieldPat {
                                       field: Field::new(i),
                                       pattern: self.lower_pattern(field),
                                   })
                    .collect();

                self.lower_variant_or_leaf(res, pat.hir_id, pat.span, ty, subpatterns)
            }

            hir::PatKind::Struct(ref qpath, ref fields, _) => {
                let res = self.tables.qpath_res(qpath, pat.hir_id);
                let subpatterns =
                    fields.iter()
                          .map(|field| {
                              FieldPat {
                                  field: Field::new(self.tcx.field_index(field.hir_id,
                                                                         self.tables)),
                                  pattern: self.lower_pattern(&field.pat),
                              }
                          })
                          .collect();

                self.lower_variant_or_leaf(res, pat.hir_id, pat.span, ty, subpatterns)
            }

            hir::PatKind::Or(ref pats) => {
                PatKind::Or {
                    pats: pats.iter().map(|p| self.lower_pattern(p)).collect(),
                }
            }
        };

        Pat {
            span: pat.span,
            ty,
            kind: Box::new(kind),
        }
    }

    fn lower_patterns(&mut self, pats: &'tcx [P<hir::Pat>]) -> Vec<Pat<'tcx>> {
        pats.iter().map(|p| self.lower_pattern(p)).collect()
    }

    fn lower_opt_pattern(&mut self, pat: &'tcx Option<P<hir::Pat>>) -> Option<Pat<'tcx>>
    {
        pat.as_ref().map(|p| self.lower_pattern(p))
    }

    fn flatten_nested_slice_patterns(
        &mut self,
        prefix: Vec<Pat<'tcx>>,
        slice: Option<Pat<'tcx>>,
        suffix: Vec<Pat<'tcx>>)
        -> (Vec<Pat<'tcx>>, Option<Pat<'tcx>>, Vec<Pat<'tcx>>)
    {
        let orig_slice = match slice {
            Some(orig_slice) => orig_slice,
            None => return (prefix, slice, suffix)
        };
        let orig_prefix = prefix;
        let orig_suffix = suffix;

        // dance because of intentional borrow-checker stupidity.
        let kind = *orig_slice.kind;
        match kind {
            PatKind::Slice { prefix, slice, mut suffix } |
            PatKind::Array { prefix, slice, mut suffix } => {
                let mut orig_prefix = orig_prefix;

                orig_prefix.extend(prefix);
                suffix.extend(orig_suffix);

                (orig_prefix, slice, suffix)
            }
            _ => {
                (orig_prefix, Some(Pat {
                    kind: box kind, ..orig_slice
                }), orig_suffix)
            }
        }
    }

    fn slice_or_array_pattern(
        &mut self,
        span: Span,
        ty: Ty<'tcx>,
        prefix: &'tcx [P<hir::Pat>],
        slice: &'tcx Option<P<hir::Pat>>,
        suffix: &'tcx [P<hir::Pat>])
        -> PatKind<'tcx>
    {
        let prefix = self.lower_patterns(prefix);
        let slice = self.lower_opt_pattern(slice);
        let suffix = self.lower_patterns(suffix);
        let (prefix, slice, suffix) =
            self.flatten_nested_slice_patterns(prefix, slice, suffix);

        match ty.kind {
            ty::Slice(..) => {
                // matching a slice or fixed-length array
                PatKind::Slice { prefix: prefix, slice: slice, suffix: suffix }
            }

            ty::Array(_, len) => {
                // fixed-length array
                let len = len.eval_usize(self.tcx, self.param_env);
                assert!(len >= prefix.len() as u64 + suffix.len() as u64);
                PatKind::Array { prefix: prefix, slice: slice, suffix: suffix }
            }

            _ => {
                span_bug!(span, "bad slice pattern type {:?}", ty);
            }
        }
    }

    fn lower_variant_or_leaf(
        &mut self,
        res: Res,
        hir_id: hir::HirId,
        span: Span,
        ty: Ty<'tcx>,
        subpatterns: Vec<FieldPat<'tcx>>,
    ) -> PatKind<'tcx> {
        let res = match res {
            Res::Def(DefKind::Ctor(CtorOf::Variant, ..), variant_ctor_id) => {
                let variant_id = self.tcx.parent(variant_ctor_id).unwrap();
                Res::Def(DefKind::Variant, variant_id)
            },
            res => res,
        };

        let mut kind = match res {
            Res::Def(DefKind::Variant, variant_id) => {
                let enum_id = self.tcx.parent(variant_id).unwrap();
                let adt_def = self.tcx.adt_def(enum_id);
                if adt_def.is_enum() {
                    let substs = match ty.kind {
                        ty::Adt(_, substs) |
                        ty::FnDef(_, substs) => substs,
                        ty::Error => {  // Avoid ICE (#50585)
                            return PatKind::Wild;
                        }
                        _ => bug!("inappropriate type for def: {:?}", ty),
                    };
                    PatKind::Variant {
                        adt_def,
                        substs,
                        variant_index: adt_def.variant_index_with_id(variant_id),
                        subpatterns,
                    }
                } else {
                    PatKind::Leaf { subpatterns }
                }
            }

            Res::Def(DefKind::Struct, _)
            | Res::Def(DefKind::Ctor(CtorOf::Struct, ..), _)
            | Res::Def(DefKind::Union, _)
            | Res::Def(DefKind::TyAlias, _)
            | Res::Def(DefKind::AssocTy, _)
            | Res::SelfTy(..)
            | Res::SelfCtor(..) => {
                PatKind::Leaf { subpatterns }
            }

            _ => {
                self.errors.push(PatternError::NonConstPath(span));
                PatKind::Wild
            }
        };

        if let Some(user_ty) = self.user_substs_applied_to_ty_of_hir_id(hir_id) {
            debug!("lower_variant_or_leaf: kind={:?} user_ty={:?} span={:?}", kind, user_ty, span);
            kind = PatKind::AscribeUserType {
                subpattern: Pat {
                    span,
                    ty,
                    kind: Box::new(kind),
                },
                ascription: Ascription {
                    user_ty: PatTyProj::from_user_type(user_ty),
                    user_ty_span: span,
                    variance: ty::Variance::Covariant,
                },
            };
        }

        kind
    }

    /// Takes a HIR Path. If the path is a constant, evaluates it and feeds
    /// it to `const_to_pat`. Any other path (like enum variants without fields)
    /// is converted to the corresponding pattern via `lower_variant_or_leaf`.
    fn lower_path(&mut self,
                  qpath: &hir::QPath,
                  id: hir::HirId,
                  span: Span)
                  -> Pat<'tcx> {
        let ty = self.tables.node_type(id);
        let res = self.tables.qpath_res(qpath, id);
        let is_associated_const = match res {
            Res::Def(DefKind::AssocConst, _) => true,
            _ => false,
        };
        let kind = match res {
            Res::Def(DefKind::Const, def_id) | Res::Def(DefKind::AssocConst, def_id) => {
                let substs = self.tables.node_substs(id);
                match ty::Instance::resolve(
                    self.tcx,
                    self.param_env,
                    def_id,
                    substs,
                ) {
                    Some(instance) => {
                        let cid = GlobalId {
                            instance,
                            promoted: None,
                        };
                        match self.tcx.at(span).const_eval(self.param_env.and(cid)) {
                            Ok(value) => {
                                // We wait until after const_eval to do this
                                // check (even though we don't need the
                                // resulting `value` to run this code), so that
                                // users with erroneous const-eval code get
                                // those diagnostics alone, rather than noise
                                // about structural match.
                                self.tcx.infer_ctxt().enter(|infcx| {
                                    let const_def_id = instance.def_id();
                                    if const_def_id.is_local() {
                                        walk_const_definition_looking_for_nonstructural_adt(
                                            &infcx, self.param_env, const_def_id, id, span);
                                    } else {
                                        // FIXME: do we need to inspect result of this call?
                                        check_const_ty_is_okay_for_structural_pattern(
                                            infcx.tcx, self.param_env, &infcx, ty, id, span);
                                    }
                                });

                                let pattern = self.const_to_pat(instance, value, id, span);
                                if !is_associated_const {
                                    return pattern;
                                }

                                let user_provided_types = self.tables().user_provided_types();
                                return if let Some(u_ty) = user_provided_types.get(id) {
                                    let user_ty = PatTyProj::from_user_type(*u_ty);
                                    Pat {
                                        span,
                                        kind: Box::new(
                                            PatKind::AscribeUserType {
                                                subpattern: pattern,
                                                ascription: Ascription {
                                                    /// Note that use `Contravariant` here. See the
                                                    /// `variance` field documentation for details.
                                                    variance: ty::Variance::Contravariant,
                                                    user_ty,
                                                    user_ty_span: span,
                                                },
                                            }
                                        ),
                                        ty: value.ty,
                                    }
                                } else {
                                    pattern
                                }
                            },
                            Err(_) => {
                                self.tcx.sess.span_err(
                                    span,
                                    "could not evaluate constant pattern",
                                );
                                PatKind::Wild
                            }
                        }
                    },
                    None => {
                        self.errors.push(if is_associated_const {
                            PatternError::AssocConstInPattern(span)
                        } else {
                            PatternError::StaticInPattern(span)
                        });
                        PatKind::Wild
                    },
                }
            }
            _ => self.lower_variant_or_leaf(res, id, span, ty, vec![]),
        };

        Pat {
            span,
            ty,
            kind: Box::new(kind),
        }
    }

    /// Converts literals, paths and negation of literals to patterns.
    /// The special case for negation exists to allow things like `-128_i8`
    /// which would overflow if we tried to evaluate `128_i8` and then negate
    /// afterwards.
    fn lower_lit(&mut self, expr: &'tcx hir::Expr) -> PatKind<'tcx> {
        match expr.kind {
            hir::ExprKind::Lit(ref lit) => {
                let ty = self.tables.expr_ty(expr);
                match lit_to_const(&lit.node, self.tcx, ty, false) {
                    Ok(val) => {
                        let instance = ty::Instance::new(
                            self.tables.local_id_root.expect("literal outside any scope"),
                            self.substs,
                        );
                        *self.const_to_pat(instance, val, expr.hir_id, lit.span).kind
                    },
                    Err(LitToConstError::UnparseableFloat) => {
                        self.errors.push(PatternError::FloatBug);
                        PatKind::Wild
                    },
                    Err(LitToConstError::Reported) => PatKind::Wild,
                }
            },
            hir::ExprKind::Path(ref qpath) => *self.lower_path(qpath, expr.hir_id, expr.span).kind,
            hir::ExprKind::Unary(hir::UnNeg, ref expr) => {
                let ty = self.tables.expr_ty(expr);
                let lit = match expr.kind {
                    hir::ExprKind::Lit(ref lit) => lit,
                    _ => span_bug!(expr.span, "not a literal: {:?}", expr),
                };
                match lit_to_const(&lit.node, self.tcx, ty, true) {
                    Ok(val) => {
                        let instance = ty::Instance::new(
                            self.tables.local_id_root.expect("literal outside any scope"),
                            self.substs,
                        );
                        *self.const_to_pat(instance, val, expr.hir_id, lit.span).kind
                    },
                    Err(LitToConstError::UnparseableFloat) => {
                        self.errors.push(PatternError::FloatBug);
                        PatKind::Wild
                    },
                    Err(LitToConstError::Reported) => PatKind::Wild,
                }
            }
            _ => span_bug!(expr.span, "not a literal: {:?}", expr),
        }
    }

    /// Converts an evaluated constant to a pattern (if possible).
    /// This means aggregate values (like structs and enums) are converted
    /// to a pattern that matches the value (as if you'd compared via structural equality).
    fn const_to_pat(
        &self,
        instance: ty::Instance<'tcx>,
        cv: &'tcx ty::Const<'tcx>,
        id: hir::HirId,
        span: Span,
    ) -> Pat<'tcx> {
        // This method is just a warpper handling a validity check; the heavy lifting is
        // performed by the recursive const_to_pat_inner method, which is not meant to be
        // invoked except by this method.
        //
        // once indirect_structural_match is a full fledged error, this
        // level of indirection can be eliminated
        //
        // FIXME do the above

        debug!("const_to_pat: cv={:#?} id={:?}", cv, id);
        debug!("const_to_pat: cv.ty={:?} span={:?}", cv.ty, span);

        let mut saw_error = false;
        let inlined_const_as_pat = self.const_to_pat_inner(instance, cv, id, span, &mut saw_error);

        return inlined_const_as_pat;
    }

    /// Recursive helper for `const_to_pat`; invoke that (instead of calling this directly).
    fn const_to_pat_inner(
        &self,
        instance: ty::Instance<'tcx>,
        cv: &'tcx ty::Const<'tcx>,
        id: hir::HirId,
        span: Span,
        // This tracks if we signal some hard error for a given const
        // value, so that we will not subsequently issue an irrelevant
        // lint for the same const value.
        saw_const_match_error: &mut bool,
    ) -> Pat<'tcx> {

        let mut adt_subpattern = |i, variant_opt| {
            let field = Field::new(i);
            let val = crate::const_eval::const_field(
                self.tcx, self.param_env, variant_opt, field, cv
            );
            self.const_to_pat_inner(instance, val, id, span, saw_const_match_error)
        };
        let mut adt_subpatterns = |n, variant_opt| {
            (0..n).map(|i| {
                let field = Field::new(i);
                FieldPat {
                    field,
                    pattern: adt_subpattern(i, variant_opt),
                }
            }).collect::<Vec<_>>()
        };


        let kind = match cv.ty.kind {
            ty::Float(_) => {
                self.tcx.lint_hir(
                    ::rustc::lint::builtin::ILLEGAL_FLOATING_POINT_LITERAL_PATTERN,
                    id,
                    span,
                    "floating-point types cannot be used in patterns",
                );
                PatKind::Constant {
                    value: cv,
                }
            }
            ty::Adt(adt_def, _) if adt_def.is_union() => {
                // Matching on union fields is unsafe, we can't hide it in constants
                *saw_const_match_error = true;
                self.tcx.sess.span_err(span, "cannot use unions in constant patterns");
                PatKind::Wild
            }
            // keep old code until future-compat upgraded to errors.
            ty::Adt(adt_def, _) if !self.tcx.has_attr(adt_def.did, sym::structural_match) => {
                let path = self.tcx.def_path_str(adt_def.did);
                let msg = format!(
                    "to use a constant of type `{}` in a pattern, \
                     `{}` must be annotated with `#[derive(PartialEq, Eq)]`",
                    path,
                    path,
                );
                *saw_const_match_error = true;
                self.tcx.sess.span_err(span, &msg);
                PatKind::Wild
            }
            // keep old code until future-compat upgraded to errors.
            ty::Ref(_, ty::TyS { kind: ty::Adt(adt_def, _), .. }, _)
            if !self.tcx.has_attr(adt_def.did, sym::structural_match) => {
                // HACK(estebank): Side-step ICE #53708, but anything other than erroring here
                // would be wrong. Returnging `PatKind::Wild` is not technically correct.
                let path = self.tcx.def_path_str(adt_def.did);
                let msg = format!(
                    "to use a constant of type `{}` in a pattern, \
                     `{}` must be annotated with `#[derive(PartialEq, Eq)]`",
                    path,
                    path,
                );
                *saw_const_match_error = true;
                self.tcx.sess.span_err(span, &msg);
                PatKind::Wild
            }
            ty::Adt(adt_def, substs) if adt_def.is_enum() => {
                let variant_index = const_variant_index(self.tcx, self.param_env, cv);
                let subpatterns = adt_subpatterns(
                    adt_def.variants[variant_index].fields.len(),
                    Some(variant_index),
                );
                PatKind::Variant {
                    adt_def,
                    substs,
                    variant_index,
                    subpatterns,
                }
            }
            ty::Adt(adt_def, _) => {
                let struct_var = adt_def.non_enum_variant();
                PatKind::Leaf {
                    subpatterns: adt_subpatterns(struct_var.fields.len(), None),
                }
            }
            ty::Tuple(fields) => {
                PatKind::Leaf {
                    subpatterns: adt_subpatterns(fields.len(), None),
                }
            }
            ty::Array(_, n) => {
                PatKind::Array {
                    prefix: (0..n.eval_usize(self.tcx, self.param_env))
                        .map(|i| adt_subpattern(i as usize, None))
                        .collect(),
                    slice: None,
                    suffix: Vec::new(),
                }
            }
            _ => {
                PatKind::Constant {
                    value: cv,
                }
            }
        };

        Pat {
            span,
            ty: cv.ty,
            kind: Box::new(kind),
        }
    }
}

// FIXME Move `struct ExprVisitor` out here and then make this a method on it,
// so that the hir::intravisit::Visitor::visit_expr method can recursively call
// it directly. (All args but `def_id` can be part of `self` then.)
fn walk_const_definition_looking_for_nonstructural_adt(infcx: &'a InferCtxt<'a, 'tcx>,
                                                       param_env: ty::ParamEnv<'tcx>,
                                                       def_id: hir::def_id::DefId,
                                                       id: hir::HirId,
                                                       span: Span)
{
    // Traverses right-hand side of const definition, looking for:
    //
    // 1. literals constructing ADTs that do not implement `Structural`
    //    (rust-lang/rust#62614), and
    //
    // 2. non-scalar types that do not implement `PartialEq` (which would
    //    cause codegen to ICE).

    debug!("walk_const_value_looking_for_nonstructural_adt \
            def_id: {:?} id: {:?} span: {:?}", def_id, id, span);

    assert!(def_id.is_local());
    let const_hir_id: hir::HirId = infcx.tcx.hir().local_def_id_to_hir_id(def_id.to_local());
    debug!("walk_const_value_looking_for_nonstructural_adt const_hir_id: {:?}", const_hir_id);
    let body_id = infcx.tcx.hir().body_owned_by(const_hir_id);
    debug!("walk_const_value_looking_for_nonstructural_adt body_id: {:?}", body_id);
    let body_tables = infcx.tcx.body_tables(body_id);
    let body = infcx.tcx.hir().body(body_id);
    let mut v = ExprVisitor {
        infcx, param_env, body_tables, id, span,
        fulfillment_cx: traits::FulfillmentContext::new(),
    };
    v.visit_body(body);
    if let Err(err) = v.fulfillment_cx.select_all_or_error(&v.infcx) {
        v.infcx.report_fulfillment_errors(&err, None, false);
    }
    return;

    struct ExprVisitor<'a, 'tcx> {
        infcx: &'a InferCtxt<'a, 'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        body_tables: &'a ty::TypeckTables<'tcx>,
        fulfillment_cx: traits::FulfillmentContext<'tcx>,
        id: hir::HirId,
        span: Span,
    }

    use hir::intravisit::{self, Visitor, NestedVisitorMap};

    impl<'a, 'v, 'tcx> Visitor<'v> for ExprVisitor<'a, 'tcx> {
        fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'v>
        {
            NestedVisitorMap::None
        }
        fn visit_expr(&mut self, ex: &'v hir::Expr) {
            debug!("walk_const_value_looking_for_nonstructural_adt ExprVisitor ex: {:?}", ex);
            let ty = self.body_tables.expr_ty(ex);
            debug!("walk_const_value_looking_for_nonstructural_adt ExprVisitor ex: {:?} ty: {}",
                   ex, ty);
            if let hir::ExprKind::Struct(..) = ex.kind {
                debug!("walk_const_value_looking_for_nonstructural_adt \
                        ExprKind::Struct: registering Structural bound");

                let cause = ObligationCause::new(self.span, self.id, ConstPatternStructural);
                let structural_def_id = self.infcx.tcx.lang_items().structural_trait().unwrap();
                self.fulfillment_cx.register_bound(
                    &self.infcx, self.param_env, ty, structural_def_id, cause);
            }

            // When we inspect the expression, we may or may not choose to
            // inspecting its type recursively. If we do inspect the type, then
            // that will impose its own `PartialEq` requirement. But if we don't
            // inspect the type, then we should add our own imposition of that
            // requirement.
            //
            // FIXME the requirement being imposed here may or may not need to
            // be treated as a lint (rather than a hard requirement).
            let mut checked_ty = false;

            debug!("walk_const_value_looking_for_nonstructural_adt ex.kind: {:?}", ex.kind);

            match &ex.kind {
                hir::ExprKind::Path(qpath) => {
                    debug!("walk_const_value_looking_for_nonstructural_adt resolve path");
                    let res = self.body_tables.qpath_res(qpath, ex.hir_id);
                    match res {
                        Res::Def(DefKind::Const, def_id) |
                        Res::Def(DefKind::AssocConst, def_id) => {
                            debug!("walk_const_value_looking_for_nonstructural_adt \
                                    ExprKind::Path res: {:?} const", res);

                            let substs = self.body_tables.node_substs(ex.hir_id);
                            if let Some(instance) = ty::Instance::resolve(
                                self.infcx.tcx, self.param_env, def_id, substs)
                            {

                                let const_def_id = instance.def_id();
                                if const_def_id.is_local() {
                                    debug!("walk_const_value_looking_for_nonstructural_adt \
                                            recursively check instance: {:?} def_id: {:?}",
                                           instance, def_id);
                                    walk_const_definition_looking_for_nonstructural_adt(
                                        &self.infcx, self.param_env, const_def_id,
                                        self.id, self.span);
                                } else {
                                    // FIXME: do we need to inspect result of this call?
                                    debug!("walk_const_value_looking_for_nonstructural_adt \
                                            use type analysis on instance: {:?} def_id: {:?}",
                                           instance, def_id);
                                    check_const_ty_is_okay_for_structural_pattern(
                                        self.infcx.tcx, self.param_env, &self.infcx, ty,
                                        self.id, self.span);
                                }
                            } else {
                                debug!("walk_const_value_looking_for_nonstructural_adt \
                                        failed to resolve const def_id: {:?}; \
                                        skipping code under assumption it is erroneous", def_id);
                                self.infcx.tcx.sess.delay_span_bug(self.span, &format!(
                                    "walk_const_value_looking_for_nonstructural_adt \
                                     didn't resolve def_id: {:?}", def_id));
                            }
                        }
                        Res::Def(DefKind::Ctor(..), _def_id) => {
                            debug!("walk_const_value_looking_for_nonstructural_adt \
                                    ExprKind::Path res: {:?} registering Structural bound", res);

                            let cause = ObligationCause::new(
                                self.span, self.id, ConstPatternStructural);
                            let structural_def_id =
                                self.infcx.tcx.lang_items().structural_trait().unwrap();
                            self.fulfillment_cx.register_bound(
                                &self.infcx, self.param_env, ty, structural_def_id, cause);
                        }

                        _ => {
                            debug!("walk_const_value_looking_for_nonstructural_adt \
                                    ExprKind::Path res: {:?} traverse type instead", res);
                        }
                    }
                }

                hir::ExprKind::Box(..) |
                hir::ExprKind::Array(..) |
                hir::ExprKind::Repeat(..) |
                hir::ExprKind::Struct(..) |
                hir::ExprKind::Tup(..) |
                hir::ExprKind::Type(..) |
                hir::ExprKind::DropTemps(..) |
                hir::ExprKind::AddrOf(..) => {
                    // continue expression-based traversal
                    debug!("walk_const_value_looking_for_nonstructural_adt full recur");

                    intravisit::walk_expr(self, ex)
                }

                hir::ExprKind::Block(block, _opt_label) => {
                    debug!("walk_const_value_looking_for_nonstructural_adt recur on block tail");
                    // skip the statements, focus solely on the return expression
                    if let Some(ex) = &block.expr {
                        intravisit::walk_expr(self, ex)
                    }
                }

                hir::ExprKind::Match(_input, arms, _match_source) => {
                    debug!("walk_const_value_looking_for_nonstructural_adt recur on arm bodies");
                    // skip the input, focus solely on the arm bodies
                    for a in arms.iter() {
                        intravisit::walk_expr(self, &a.body)
                    }
                }

                hir::ExprKind::Loop(..) |
                hir::ExprKind::Call(..) |
                hir::ExprKind::MethodCall(..) |
                hir::ExprKind::Binary(..) |
                hir::ExprKind::Unary(..) |
                hir::ExprKind::Cast(..) |
                hir::ExprKind::Closure(..) |
                hir::ExprKind::Assign(..) |
                hir::ExprKind::AssignOp(..) |
                hir::ExprKind::Field(..) |
                hir::ExprKind::Index(..) |
                hir::ExprKind::Break(..) |
                hir::ExprKind::Continue(..) |
                hir::ExprKind::Ret(..) |
                hir::ExprKind::Yield(..) |
                hir::ExprKind::InlineAsm(..) |
                hir::ExprKind::Lit(..) |
                hir::ExprKind::Err => {
                    debug!("walk_const_value_looking_for_nonstructural_adt traverse type instead");
                    // abstraction barrer; do *not* traverse the expression.
                    // Instead, resort to (conservative) traversal of
                    // `typeof(expr)` here.

                    // FIXME: merge the two visitor structs, unify the result codes.
                    check_const_ty_is_okay_for_structural_pattern(
                        self.infcx.tcx, self.param_env, &self.infcx, ty, self.id, self.span);
                    checked_ty = true;
                }
            }

            if !checked_ty && !ty.is_scalar() {
                debug!("walk_const_value_looking_for_nonstructural_adt \
                        non-scalar ty: registering PartialEq bound");

                let cause = ObligationCause::new(self.span, self.id,
                                                 ConstPatternStructural);
                let partial_eq_def_id = self.infcx.tcx.lang_items().eq_trait().unwrap();

                // Note: Cannot use register_bound here, because it requires
                // (but does not check) that the given trait has no type
                // parameters apart from `Self`, but `PartialEq` has a type
                // parameter that defaults to `Self`.
                let trait_ref = ty::TraitRef {
                    def_id: partial_eq_def_id,
                    substs: self.infcx.tcx.mk_substs_trait(ty, &[ty.into()]),
                };
                self.fulfillment_cx.register_predicate_obligation(
                    &self.infcx,
                    traits::Obligation {
                        cause,
                        recursion_depth: 0,
                        param_env: self.param_env,
                        predicate: trait_ref.to_predicate(),
                    });
            }
        }
    }
}

fn is_partial_eq(tcx: TyCtxt<'tcx>,
                 param_env: ty::ParamEnv<'tcx>,
                 infcx: &InferCtxt<'a, 'tcx>,
                 ty: Ty<'tcx>,
                 id: hir::HirId,
                 span: Span)
                 -> bool
{
    let partial_eq_trait_id = tcx.lang_items().eq_trait().unwrap();
    let obligation: PredicateObligation<'_> =
        tcx.predicate_for_trait_def(param_env,
                                    ObligationCause::misc(span, id),
                                    partial_eq_trait_id,
                                    0,
                                    ty,
                                    &[]);
    // FIXME: should this call a `predicate_must_hold` variant instead?
    infcx.predicate_may_hold(&obligation)
}

#[derive(Copy, Clone)]
enum CheckConstForStructuralPattern {
    // The check succeeded. The const followed the rules for use in a pattern
    // (or at least all rules from lints are currently checking), and codegen
    // should be fine.
    Ok,

    // Reported an error that has always been unrecoverable (i.e. causes codegen
    // problems). In this case, can just produce a wild pattern and move along
    // (rather than ICE'ing further down).
    ReportedNonrecoverableError,

    // Reported a diagnostic that rustc can recover from (e.g. the current
    // requirement that `const` in patterns uses structural equality)
    ReportedRecoverableLint,

    // The given constant does not actually implement `PartialEq`. This
    // unfortunately has been allowed in certain scenarios in stable Rust, and
    // therefore we cannot currently treat it as an error.
    UnreportedNonpartialEq,
}

/// This method traverses the structure of `ty`, trying to find an
/// instance of an ADT (i.e. struct or enum) that does not implement
/// the `Structural` trait.
///
/// The "structure of a type" includes all components that would be
/// considered when doing a pattern match on a constant of that
/// type.
///
///  * This means this method descends into fields of structs/enums,
///    and also descends into the inner type `T` of `&T` and `&mut T`
///
///  * The traversal doesn't dereference unsafe pointers (`*const T`,
///    `*mut T`), and it does not visit the type arguments of an
///    instantiated generic like `PhantomData<T>`.
///
/// The reason we do this search is Rust currently require all ADT's
/// reachable from a constant's type to implement `Structural`, a
/// trait which essentially says that the implementation of
/// `PartialEq::eq` behaves *equivalently* to a comparison against
/// the unfolded structure.
///
/// For more background on why Rust has this requirement, and issues
/// that arose when the requirement was not enforced completely, see
/// Rust RFC 1445, rust-lang/rust#61188, and rust-lang/rust#62307.
fn check_const_ty_is_okay_for_structural_pattern(
    tcx: TyCtxt<'tcx>, // FIXME if we pass infcx then remove this param
    param_env: ty::ParamEnv<'tcx>,
    infcx: &'a InferCtxt<'a, 'tcx>,
    ty: Ty<'tcx>,
    id: hir::HirId,
    span: Span)
    -> CheckConstForStructuralPattern
{
    // Import here (not mod level), because `TypeFoldable::fold_with`
    // conflicts with `PatternFoldable::fold_with`
    use crate::rustc::ty::fold::TypeVisitor;
    use crate::rustc::ty::TypeFoldable;

    let ty_is_partial_eq: bool = is_partial_eq(tcx, param_env, infcx, ty, id, span);

    let mut search = Search {
        tcx, param_env, infcx, id, span,
        fulfillment_cx: traits::FulfillmentContext::new(),
        found: None,
        seen: FxHashSet::default(),
    };

    // FIXME (#62614): instead of this traversal of the type, we should probably
    // traverse the `const` definition and query (solely) the types that occur
    // in the definition itself.
    ty.visit_with(&mut search);

    let reported_fulfillment_errors;
    match search.fulfillment_cx.select_all_or_error(search.infcx) {
        Err(err) => {
            assert!(!ty_is_partial_eq);
            search.infcx.report_fulfillment_errors(&err, None, false);
            reported_fulfillment_errors = true;
        }
        Ok(_) => {
            reported_fulfillment_errors = false;
        }
    }

    let check_result = if let Some(adt_def) = search.found {
        let path = tcx.def_path_str(adt_def.did);
        let msg = format!(
            "to use a constant of type `{}` in a pattern, \
             `{}` must be annotated with `#[derive(PartialEq, Eq)]`",
            path,
            path,
        );

        // FIXME: maybe use reported_fulfillment_errors as the boolean test here.
        if !search.is_partial_eq(ty) {
            // span_fatal avoids ICE from resolution of non-existent method (rare case).
            tcx.sess.span_fatal(span, &msg);
        } else {
            tcx.lint_hir(lint::builtin::INDIRECT_STRUCTURAL_MATCH, id, span, &msg);
            CheckConstForStructuralPattern::ReportedRecoverableLint
        }
    } else {
        // if all ADTs in the const were structurally matchable, then we would
        // like to conclude the type must implement `PartialEq`. But cases like
        // rust-lang/rust#61188 show cases where this did not hold, because the
        // structural_match analysis will not necessariy observe the type
        // parameters, while deriving `PartialEq` always requires the parameters
        // to themselves implement `PartialEq`.

        if reported_fulfillment_errors {
            // If we *did* report an error, then we don't need to try to produce
            // backwards-compatible code-gen.
            CheckConstForStructuralPattern::ReportedNonrecoverableError
        } else if ty_is_partial_eq {
            // if all ADTs in the const were structurally matchable and all
            // non-scalars implement `PartialEq`, then you would think we were
            // definitely in a case where the type itself must implement
            // `PartialEq` (and therefore could safely `assert!(ty_is_partial_eq)`
            // here).
            //
            // However, exceptions to this exist (like `fn(&T)`, which is sugar
            // for `for <'a> fn(&'a T)`); see rust-lang/rust#46989.
            //
            // For now, let compilation continue, under assumption that compiler
            // will ICE if codegen is actually impossible.
            CheckConstForStructuralPattern::Ok
        } else {
            CheckConstForStructuralPattern::UnreportedNonpartialEq
        }
    };

    return check_result;

    struct Search<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        infcx: &'a InferCtxt<'a, 'tcx>,
        fulfillment_cx: traits::FulfillmentContext<'tcx>,

        id: hir::HirId,
        span: Span,

        // records the first ADT we find that does not implement `Structural`.
        found: Option<&'tcx AdtDef>,

        // tracks ADT's previously encountered during search, so that
        // we will not recur on them again.
        seen: FxHashSet<&'tcx AdtDef>,
    }

    impl<'a, 'tcx> Search<'a, 'tcx> {
        fn is_partial_eq(&self, ty: Ty<'tcx>) -> bool {
            is_partial_eq(self.tcx, self.param_env, &self.infcx, ty, self.id, self.span)
        }
    }

    impl<'a, 'tcx> TypeVisitor<'tcx> for Search<'a, 'tcx> {
        fn visit_ty(&mut self, ty: Ty<'tcx>) -> bool {
            debug!("Search visiting ty: {:?}", ty);

            let (adt_def, substs) = match ty.kind {
                ty::Adt(adt_def, substs) => (adt_def, substs),
                ty::RawPtr(..) => {
                    // `#[structural_match]` ignores substructure of
                    // `*const _`/`*mut _`, so skip super_visit_with
                    //
                    // (But still tell caller to continue search.)
                    return false;
                }
                ty::FnDef(..) | ty::FnPtr(..) => {
                    // types of formals and return in `fn(_) -> _` are also irrelevant
                    //
                    // (But still tell caller to continue search.)
                    return false;
                }
                ty::Array(_, n) if n.try_eval_usize(self.tcx, ty::ParamEnv::reveal_all()) == Some(0)
                => {
                    // rust-lang/rust#62336: ignore type of contents
                    // for empty array.
                    return false;
                }
                _ => {
                    if !ty.is_scalar() {
                        debug!("Search registering PartialEq bound for non-scalar ty: {}", ty);
                        let cause = ObligationCause::new(self.span, self.id,
                                                         ConstPatternStructural);
                        let partial_eq_def_id = self.tcx.lang_items().eq_trait().unwrap();

                        // Note: Cannot use register_bound here, because it
                        // requires (but does not check) that the given trait
                        // has no type parameters apart from `Self`, but
                        // `PartialEq` has a type parameter that defaults to
                        // `Self`.
                        let trait_ref = ty::TraitRef {
                            def_id: partial_eq_def_id,
                            substs: self.tcx.mk_substs_trait(ty, &[ty.into()]),
                        };
                        self.fulfillment_cx.register_predicate_obligation(
                            &self.infcx,
                            traits::Obligation {
                                cause,
                                recursion_depth: 0,
                                param_env: self.param_env,
                                predicate: trait_ref.to_predicate(),
                            });
                    }

                    ty.super_visit_with(self);
                    return false;
                }
            };

            if self.seen.contains(adt_def) {
                debug!("Search already seen adt_def: {:?}", adt_def);
                // let caller continue its search
                return false;
            }

            {
                debug!("Search registering Structural bound for adt ty: {}", ty);

                let cause = ObligationCause::new(self.span, self.id, ConstPatternStructural);
                let structural_def_id = self.tcx.lang_items().structural_trait().unwrap();
                self.fulfillment_cx.register_bound(
                    &self.infcx, self.param_env, ty, structural_def_id, cause);

                // We deliberately do not report fulfillment errors related to
                // this check, becase we want the diagnostics to be controlled
                // by a future-compatibility lint. (Also current implementation
                // is conservative and would flag too many false positives; see
                // e.g. rust-lang/rust#62614.)
                if self.fulfillment_cx.select_all_or_error(&self.infcx).is_err() {
                    debug!("Search found ty: {:?}", ty);
                    self.found = Some(&adt_def);
                    return true // Halt visiting!
                }
            }

            self.seen.insert(adt_def);

            // `#[structural_match]` does not care about the
            // instantiation of the generics in an ADT (it
            // instead looks directly at its fields outside
            // this match), so we skip super_visit_with.
            //
            // (Must not recur on substs for `PhantomData<T>` cf
            // rust-lang/rust#55028 and rust-lang/rust#55837; but also
            // want to skip substs when only uses of generic are
            // behind unsafe pointers `*const T`/`*mut T`.)

            // even though we skip super_visit_with, we must recur on fields of
            // ADT (at least while we traversing type structure rather than
            // const definition).
            let tcx = self.tcx;
            for field_ty in adt_def.all_fields().map(|field| field.ty(tcx, substs)) {
                if field_ty.visit_with(self) {
                    // found a non-structural ADT; halt visiting!
                    assert!(self.found.is_some());
                    return true;
                }
            }

            // Even though we do not want to recur on substs, we do
            // want our caller to continue its own search.
            false
        }
    }
}

impl UserAnnotatedTyHelpers<'tcx> for PatCtxt<'_, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn tables(&self) -> &ty::TypeckTables<'tcx> {
        self.tables
    }
}


pub trait PatternFoldable<'tcx> : Sized {
    fn fold_with<F: PatternFolder<'tcx>>(&self, folder: &mut F) -> Self {
        self.super_fold_with(folder)
    }

    fn super_fold_with<F: PatternFolder<'tcx>>(&self, folder: &mut F) -> Self;
}

pub trait PatternFolder<'tcx> : Sized {
    fn fold_pattern(&mut self, pattern: &Pat<'tcx>) -> Pat<'tcx> {
        pattern.super_fold_with(self)
    }

    fn fold_pattern_kind(&mut self, kind: &PatKind<'tcx>) -> PatKind<'tcx> {
        kind.super_fold_with(self)
    }
}


impl<'tcx, T: PatternFoldable<'tcx>> PatternFoldable<'tcx> for Box<T> {
    fn super_fold_with<F: PatternFolder<'tcx>>(&self, folder: &mut F) -> Self {
        let content: T = (**self).fold_with(folder);
        box content
    }
}

impl<'tcx, T: PatternFoldable<'tcx>> PatternFoldable<'tcx> for Vec<T> {
    fn super_fold_with<F: PatternFolder<'tcx>>(&self, folder: &mut F) -> Self {
        self.iter().map(|t| t.fold_with(folder)).collect()
    }
}

impl<'tcx, T: PatternFoldable<'tcx>> PatternFoldable<'tcx> for Option<T> {
    fn super_fold_with<F: PatternFolder<'tcx>>(&self, folder: &mut F) -> Self{
        self.as_ref().map(|t| t.fold_with(folder))
    }
}

macro_rules! CloneImpls {
    (<$lt_tcx:tt> $($ty:ty),+) => {
        $(
            impl<$lt_tcx> PatternFoldable<$lt_tcx> for $ty {
                fn super_fold_with<F: PatternFolder<$lt_tcx>>(&self, _: &mut F) -> Self {
                    Clone::clone(self)
                }
            }
        )+
    }
}

CloneImpls!{ <'tcx>
    Span, Field, Mutability, ast::Name, hir::HirId, usize, ty::Const<'tcx>,
    Region<'tcx>, Ty<'tcx>, BindingMode, &'tcx AdtDef,
    SubstsRef<'tcx>, &'tcx GenericArg<'tcx>, UserType<'tcx>,
    UserTypeProjection, PatTyProj<'tcx>
}

impl<'tcx> PatternFoldable<'tcx> for FieldPat<'tcx> {
    fn super_fold_with<F: PatternFolder<'tcx>>(&self, folder: &mut F) -> Self {
        FieldPat {
            field: self.field.fold_with(folder),
            pattern: self.pattern.fold_with(folder)
        }
    }
}

impl<'tcx> PatternFoldable<'tcx> for Pat<'tcx> {
    fn fold_with<F: PatternFolder<'tcx>>(&self, folder: &mut F) -> Self {
        folder.fold_pattern(self)
    }

    fn super_fold_with<F: PatternFolder<'tcx>>(&self, folder: &mut F) -> Self {
        Pat {
            ty: self.ty.fold_with(folder),
            span: self.span.fold_with(folder),
            kind: self.kind.fold_with(folder)
        }
    }
}

impl<'tcx> PatternFoldable<'tcx> for PatKind<'tcx> {
    fn fold_with<F: PatternFolder<'tcx>>(&self, folder: &mut F) -> Self {
        folder.fold_pattern_kind(self)
    }

    fn super_fold_with<F: PatternFolder<'tcx>>(&self, folder: &mut F) -> Self {
        match *self {
            PatKind::Wild => PatKind::Wild,
            PatKind::AscribeUserType {
                ref subpattern,
                ascription: Ascription {
                    variance,
                    ref user_ty,
                    user_ty_span,
                },
            } => PatKind::AscribeUserType {
                subpattern: subpattern.fold_with(folder),
                ascription: Ascription {
                    user_ty: user_ty.fold_with(folder),
                    variance,
                    user_ty_span,
                },
            },
            PatKind::Binding {
                mutability,
                name,
                mode,
                var,
                ty,
                ref subpattern,
            } => PatKind::Binding {
                mutability: mutability.fold_with(folder),
                name: name.fold_with(folder),
                mode: mode.fold_with(folder),
                var: var.fold_with(folder),
                ty: ty.fold_with(folder),
                subpattern: subpattern.fold_with(folder),
            },
            PatKind::Variant {
                adt_def,
                substs,
                variant_index,
                ref subpatterns,
            } => PatKind::Variant {
                adt_def: adt_def.fold_with(folder),
                substs: substs.fold_with(folder),
                variant_index,
                subpatterns: subpatterns.fold_with(folder)
            },
            PatKind::Leaf {
                ref subpatterns,
            } => PatKind::Leaf {
                subpatterns: subpatterns.fold_with(folder),
            },
            PatKind::Deref {
                ref subpattern,
            } => PatKind::Deref {
                subpattern: subpattern.fold_with(folder),
            },
            PatKind::Constant {
                value
            } => PatKind::Constant {
                value,
            },
            PatKind::Range(range) => PatKind::Range(range),
            PatKind::Slice {
                ref prefix,
                ref slice,
                ref suffix,
            } => PatKind::Slice {
                prefix: prefix.fold_with(folder),
                slice: slice.fold_with(folder),
                suffix: suffix.fold_with(folder)
            },
            PatKind::Array {
                ref prefix,
                ref slice,
                ref suffix
            } => PatKind::Array {
                prefix: prefix.fold_with(folder),
                slice: slice.fold_with(folder),
                suffix: suffix.fold_with(folder)
            },
            PatKind::Or { ref pats } => PatKind::Or { pats: pats.fold_with(folder) },
        }
    }
}

pub fn compare_const_vals<'tcx>(
    tcx: TyCtxt<'tcx>,
    a: &'tcx ty::Const<'tcx>,
    b: &'tcx ty::Const<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<Ordering> {
    trace!("compare_const_vals: {:?}, {:?}", a, b);

    let from_bool = |v: bool| {
        if v {
            Some(Ordering::Equal)
        } else {
            None
        }
    };

    let fallback = || from_bool(a == b);

    // Use the fallback if any type differs
    if a.ty != b.ty || a.ty != ty {
        return fallback();
    }

    let a_bits = a.try_eval_bits(tcx, param_env, ty);
    let b_bits = b.try_eval_bits(tcx, param_env, ty);

    if let (Some(a), Some(b)) = (a_bits, b_bits) {
        use ::rustc_apfloat::Float;
        return match ty.kind {
            ty::Float(ast::FloatTy::F32) => {
                let l = ::rustc_apfloat::ieee::Single::from_bits(a);
                let r = ::rustc_apfloat::ieee::Single::from_bits(b);
                l.partial_cmp(&r)
            }
            ty::Float(ast::FloatTy::F64) => {
                let l = ::rustc_apfloat::ieee::Double::from_bits(a);
                let r = ::rustc_apfloat::ieee::Double::from_bits(b);
                l.partial_cmp(&r)
            }
            ty::Int(ity) => {
                use rustc::ty::layout::{Integer, IntegerExt};
                use syntax::attr::SignedInt;
                let size = Integer::from_attr(&tcx, SignedInt(ity)).size();
                let a = sign_extend(a, size);
                let b = sign_extend(b, size);
                Some((a as i128).cmp(&(b as i128)))
            }
            _ => Some(a.cmp(&b)),
        }
    }

    if let ty::Str = ty.kind {
        match (a.val, b.val) {
            (ConstValue::Slice { .. }, ConstValue::Slice { .. }) => {
                let a_bytes = get_slice_bytes(&tcx, a.val);
                let b_bytes = get_slice_bytes(&tcx, b.val);
                return from_bool(a_bytes == b_bytes);
            }
            _ => (),
        }
    }

    fallback()
}
