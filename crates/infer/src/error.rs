use base::pp::FormatIterator;
use hir::*;
use span::{
    Span,
    diag::{Diagnostic, Label, Level},
};

use crate::constraint::{Constraint, UnifyError};

pub enum InferError<'hir> {
    TypeUnifyFail(TypeUnifyError<'hir>),
    ExprTupleLength(Span, usize, usize),
    PatTupleLength(Span, usize, usize),
    Import(&'hir std::path::Path, Diagnostic),
    ResidualConstraints(Vec<Constraint<'hir, Ty<'hir>>>),
}

impl From<InferError<'_>> for Diagnostic {
    fn from(e: InferError) -> Self {
        match e {
            InferError::TypeUnifyFail(e) => e.into(),
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
        }
    }
}

pub enum TypeUnifyError<'hir> {
    Mismatch(Ty<'hir>, Ty<'hir>),
    Occurs(UniVarId, Ty<'hir>),
    Length(usize, usize),
    Lookup(Path<'hir>),
}

impl<'hir> UnifyError<'hir, Ty<'hir>> for TypeUnifyError<'hir> {
    fn length(lhs: usize, rhs: usize) -> Self {
        Self::Length(lhs, rhs)
    }

    fn occurs(var: UniVarId, t: Ty<'hir>) -> Self {
        Self::Occurs(var, t)
    }
}

impl<'hir> From<TypeUnifyError<'hir>> for Diagnostic {
    fn from(e: TypeUnifyError<'hir>) -> Self {
        match e {
            TypeUnifyError::Mismatch(t1, t2) => Diagnostic::new(Level::Error)
                .with_message(format!("cannot unify types {t1} and {t2}"))
                .with_labels(vec![
                    Label::new(t1.span(), "type originating from here"),
                    Label::new(t2.span(), "does not match type originating from here"),
                ]),
            TypeUnifyError::Occurs(v, t) => Diagnostic::new(Level::Error)
                .with_message(format!("unification variable {v} occurs inside type {t}")),
            TypeUnifyError::Length(l1, l2) => Diagnostic::new(Level::Error).with_message(format!(
                "cannot unify type tuple of length {l1} with type tuple of length {l2}"
            )),
            TypeUnifyError::Lookup(p) => {
                Diagnostic::new(Level::Error).with_message(format!("cannot find type at path {p}"))
            }
        }
    }
}
