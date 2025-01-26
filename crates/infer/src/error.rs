use std::fmt;

use base::pp::FormatIterator;
use hir::*;
use span::{
    Span,
    diag::{Diagnostic, Label, Level},
};

use crate::constraint::Constraint;

pub enum InferError<'hir> {
    ResolveFail(Path<'hir>),
    TypeUnifyFail(UnifyError<'hir, Ty<'hir>>),
    TypeMismatch(Ty<'hir>, Ty<'hir>),
    SpecMismatch(Span, Span),
    MissingItems(Span, Span, Vec<Span>),
    ExprTupleLength(Span, usize, usize),
    PatTupleLength(Span, usize, usize),
    Import(&'hir std::path::Path, Diagnostic),
    ResidualConstraints(Vec<Constraint<'hir, Ty<'hir>>>),
    FunctorApplicationNonPath,
    FunctorApplicationNonFunctor,
}

impl From<InferError<'_>> for Diagnostic {
    fn from(e: InferError) -> Self {
        match e {
            InferError::ResolveFail(path) => Diagnostic::new(Level::Error)
                .with_message(format!("cannot find path `{path}` in this scope"))
                .with_labels(vec![Label::new(path.span(), "not found").primary()]),
            InferError::TypeUnifyFail(e) => e.into(),
            InferError::TypeMismatch(t1, t2) => Diagnostic::new(Level::Error)
                .with_message(format!("types `{t1}` and `{t2}` do not match"))
                .with_labels(vec![
                    Label::new(t1.span(), "type originating from here"),
                    Label::new(t2.span(), "does not match type originating from here"),
                ]),
            InferError::SpecMismatch(s1, s2) => Diagnostic::new(Level::Error)
                .with_message("specifications do not match")
                .with_labels(vec![
                    Label::new(s1, "this specification"),
                    Label::new(s2, "does not match specification originating from here"),
                ]),
            InferError::MissingItems(mt1, mt2, _items) => Diagnostic::new(Level::Error)
                .with_message("missing items for module type")
                .with_labels(vec![
                    Label::new(mt1, "the items specified here").primary(),
                    Label::new(mt2, "should be a superset of the items specified here"),
                ]),
            InferError::ExprTupleLength(e, l1, l2) => Diagnostic::new(Level::Error)
                .with_message(format!(
                    "tuple with length {l1} cannot be compared with a type tuple of length {l2}"
                ))
                .with_labels(vec![Label::new(e, format!("this expression has length {l1}"))]),
            InferError::PatTupleLength(p, l1, l2) => Diagnostic::new(Level::Error)
                .with_message(format!(
                    "pattern tuple with length {l1} cannot be compared with a type tuple of length {l2}"
                ))
                .with_labels(vec![Label::new(p, format!("this pattern has length {l1}"))]),
            InferError::Import(_, diag) => diag,
            InferError::ResidualConstraints(cts) => Diagnostic::new(Level::Error)
                .with_message(format!("residual constraints: {}", cts.iter().format(", "))),
            InferError::FunctorApplicationNonPath => Diagnostic::new(Level::Error)
                .with_message("cannot apply non-path module expression"),
            InferError::FunctorApplicationNonFunctor => {
                Diagnostic::new(Level::Error).with_message("cannot apply a non-functor")
            }
        }
    }
}

pub enum UnifyError<'hir, T: Substitutable<'hir>> {
    Mismatch(T, T),
    Occurs(T::Var, T),
    Length(usize, usize),
    Abstract(Path<'hir>, T),
    Lookup(Path<'hir>),
}

impl<'hir, T> From<(T::Var, T)> for UnifyError<'hir, T>
where
    T: Substitutable<'hir>,
{
    fn from((var, typ): (T::Var, T)) -> Self {
        UnifyError::Occurs(var, typ)
    }
}

impl<'hir, T> From<UnifyError<'hir, T>> for Diagnostic
where
    T: fmt::Display + Substitutable<'hir>,
{
    fn from(e: UnifyError<'hir, T>) -> Self {
        match e {
            UnifyError::Mismatch(t1, t2) => Diagnostic::new(Level::Error)
                .with_message(format!("cannot unify types {t1} and {t2}")),
            UnifyError::Occurs(v, t) => Diagnostic::new(Level::Error)
                .with_message(format!("unification variable {v} occurs inside type {t}")),
            UnifyError::Length(l1, l2) => Diagnostic::new(Level::Error).with_message(format!(
                "cannot unify type tuple of length {l1} with type tuple of length {l2}"
            )),
            UnifyError::Abstract(p, t) => Diagnostic::new(Level::Error)
                .with_message(format!("cannot unify abstract type {p} with type {t}")),
            UnifyError::Lookup(p) => {
                Diagnostic::new(Level::Error).with_message(format!("cannot find type at path {p}"))
            }
        }
    }
}
