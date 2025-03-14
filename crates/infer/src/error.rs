use base::pp::FormatIterator;
use span::{
    Span,
    diag::{Diagnostic, Label, Level},
};

use crate::{
    constraint::Constraint,
    resolve::Res,
    ty::{Ty, UniVarId},
};

pub enum InferError<'t> {
    TypeUnifyFail(TypeUnifyError<'t>),
    ExprTupleLength(Span, usize, usize),
    PatTupleLength(Span, usize, usize),
    ResidualConstraints(Vec<Constraint<'t>>),
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
            InferError::ResidualConstraints(cts) => Diagnostic::new(Level::Error)
                .with_message(format!("residual constraints: {}", cts.iter().format(", "))),
        }
    }
}

pub enum TypeUnifyError<'t> {
    Mismatch(Ty<'t>, Ty<'t>),
    Occurs(UniVarId, Ty<'t>),
    Length(usize, usize),
    Lookup(Res),
}

impl<'t> From<TypeUnifyError<'t>> for Diagnostic {
    fn from(e: TypeUnifyError<'t>) -> Self {
        match e {
            TypeUnifyError::Mismatch(t1, t2) => Diagnostic::new(Level::Error)
                .with_message(format!("cannot unify types {t1} and {t2}"))
                .with_labels(vec![
                    Label::new(t1.span(), "type originating from here"),
                    Label::new(t2.span(), "does not match type originating from here"),
                ]),
            TypeUnifyError::Occurs(v, t) => Diagnostic::new(Level::Error)
                .with_message(format!("unification variable {v} occurs inside type {t}")),
            // FIXME spans
            TypeUnifyError::Length(l1, l2) => Diagnostic::new(Level::Error).with_message(format!(
                "cannot unify type tuple of length {l1} with type tuple of length {l2}"
            )),
            // FIXME res_id -> path
            TypeUnifyError::Lookup(res_id) => Diagnostic::new(Level::Error)
                .with_message(format!("cannot find type at path {res_id:?}")),
        }
    }
}
