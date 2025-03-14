use span::diag::{Diagnostic, Label, Level};

use crate::{
    ty::{Ty, UniVarId},
    unify::Origin,
};

pub enum InferError<'t> {
    TypeUnifyFail(TypeUnifyError<'t>),
}

impl From<InferError<'_>> for Diagnostic {
    fn from(e: InferError) -> Self {
        match e {
            InferError::TypeUnifyFail(e) => e.diagnostic(),
        }
    }
}

// TODO. Type unification errors are mysterious and important.
//       We can do better with some kind of tracing mechanism.
pub struct TypeUnifyError<'t> {
    pub kind: TypeUnifyErrorKind<'t>,
    pub origin: Origin,
}

pub enum TypeUnifyErrorKind<'t> {
    Mismatch(Ty<'t>, Ty<'t>),
    Length(usize, usize),
    Occurs(UniVarId, Ty<'t>),
}

impl<'t> TypeUnifyError<'t> {
    pub fn new(kind: TypeUnifyErrorKind<'t>, origin: Origin) -> Self {
        Self { kind, origin }
    }

    fn diagnostic(self) -> Diagnostic {
        let message = match self.kind {
            TypeUnifyErrorKind::Mismatch(t1, t2) => format!("cannot unify types {t1} and {t2}"),
            TypeUnifyErrorKind::Length(l1, l2) => {
                format!("cannot unify type tuple of length {l1} with type tuple of length {l2}")
            }
            TypeUnifyErrorKind::Occurs(v, t) => {
                format!("unification variable {v} occurs inside type {t}")
            }
        };

        let labels = match self.origin {
            Origin::Generic(left_span, right_span) => {
                if left_span == right_span {
                    vec![Label::new(left_span, "").primary()]
                } else {
                    vec![
                        Label::new(left_span, "").primary(),
                        Label::new(right_span, ""),
                    ]
                }
            }
            Origin::If(span) => {
                vec![Label::new(span, "expected a boolean value for if condition").primary()]
            }
            Origin::Seq(span) => {
                vec![Label::new(span, "expected a unit value in sequence").primary()]
            }
            Origin::Vector {
                vector_span,
                elem_span,
            } => {
                vec![
                    Label::new(elem_span, "element type").primary(),
                    Label::new(vector_span, "should match vector type"),
                ]
            }
        };

        Diagnostic::new(Level::Error)
            .with_message(message)
            .with_labels(labels)
    }
}
