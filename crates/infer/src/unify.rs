use span::Span;

use crate::{
    Infer,
    error::{ArityKind, InferError, TypeUnifyError, TypeUnifyErrorKind},
    ty::{Ty, TyKind},
};

// TODO. Add more context options.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Origin {
    Generic(Span, Span),
    ConsArg(Span),
    If(Span),
    Seq(Span),
    Vector { vector_span: Span, elem_span: Span },
}

impl<'t> Infer<'t> {
    pub fn eq(&mut self, origin: Origin, lhs: Ty<'t>, rhs: Ty<'t>) -> Result<(), InferError<'t>> {
        log::trace!("[eq] {lhs} ~ {rhs} @ {:?}", origin);
        let lhs = self.instantiate(lhs);
        let rhs = self.instantiate(rhs);
        Unifier {
            infer: self,
            origin,
        }
        .unify(lhs, rhs)
        .map_err(InferError::TypeUnifyFail)
    }
}

struct Unifier<'u, 't> {
    infer: &'u mut Infer<'t>,
    origin: Origin,
}

impl<'t> Unifier<'_, 't> {
    fn unify(&mut self, lhs: Ty<'t>, rhs: Ty<'t>) -> Result<(), TypeUnifyError<'t>> {
        log::trace!("  [unify] {lhs} ~ {rhs}");
        let lhs = self.infer.subs.real(lhs);
        let rhs = self.infer.subs.real(rhs);
        log::trace!("    [real] {lhs} ~ {rhs}");
        match (lhs.as_var(), rhs.as_var()) {
            (Some(_), _) => self.infer.subs.union(lhs, rhs).map_err(|(v, t)| {
                TypeUnifyError::new(TypeUnifyErrorKind::Occurs(v, t), self.origin)
            }),
            (_, Some(_)) => self.infer.subs.union(rhs, lhs).map_err(|(v, t)| {
                TypeUnifyError::new(TypeUnifyErrorKind::Occurs(v, t), self.origin)
            }),
            (None, None) => match (*lhs.kind(), *rhs.kind()) {
                (lhs, rhs) if lhs == rhs => Ok(()),
                (TyKind::Arrow(l_args, l_ret), TyKind::Arrow(r_args, r_ret)) => {
                    self.zip_unify(ArityKind::Func, l_args, r_args)?;
                    self.unify(l_ret, r_ret)
                }
                (TyKind::App(l_res, _, l_args), TyKind::App(r_res, _, r_args))
                    if l_res == r_res =>
                {
                    self.zip_unify(ArityKind::Cons, l_args, r_args)
                }
                (TyKind::Tuple(l_ts), TyKind::Tuple(r_ts)) => {
                    self.zip_unify(ArityKind::Tuple, l_ts, r_ts)
                }
                (TyKind::Vector(l), TyKind::Vector(r)) => self.unify(l, r),
                (_, _) => Err(TypeUnifyError::new(
                    TypeUnifyErrorKind::Mismatch(lhs, rhs),
                    self.origin,
                )),
            },
        }
    }

    fn zip_unify(
        &mut self,
        kind: ArityKind,
        lhs: &[Ty<'t>],
        rhs: &[Ty<'t>],
    ) -> Result<(), TypeUnifyError<'t>> {
        if lhs.len() != rhs.len() {
            return Err(TypeUnifyError::new(
                TypeUnifyErrorKind::Arity(kind, lhs.len(), rhs.len()),
                self.origin,
            ));
        }
        for (&l, &r) in lhs.iter().zip(rhs) {
            self.unify(l, r)?;
        }
        Ok(())
    }
}
