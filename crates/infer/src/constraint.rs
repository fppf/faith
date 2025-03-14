use std::{collections::VecDeque, fmt};

use base::hash::{IndexSet, Set};
use span::Span;

use crate::{
    Infer,
    error::TypeUnifyError,
    ty::{Ty, TyKind},
};

/// Equality constraint (t1 ~ t2).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Constraint<'t> {
    pub lhs: Ty<'t>,
    pub rhs: Ty<'t>,
}

/*
impl PartialEq for Constraint<'_>
{
    fn eq(&self, other: &Self) -> bool {
        // l1 ~ r1 == l2 ~ r2 if
        //    l1 == l2 /\ r1 == r2
        // OR l1 == r2 /\ r1 == l2
        let Constraint {
            lhs: l1, rhs: r1, ..
        } = self;
        let Constraint {
            lhs: l2, rhs: r2, ..
        } = other;
        ((l1 == l2) && (r1 == r2)) || ((l1 == r2) && (r1 == l2))
    }
}
*/

impl fmt::Display for Constraint<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ~ {}", self.lhs, self.rhs)
    }
}

impl<'t> Constraint<'t> {
    #[inline]
    pub fn equal(lhs: Ty<'t>, rhs: Ty<'t>) -> Self {
        Self { lhs, rhs }
    }
}

impl<'t> Infer<'_, 't> {
    fn try_unify(&mut self, lhs: Ty<'t>, rhs: Ty<'t>) -> Result<(), TypeUnifyError<'t>> {
        let lhs = self.subs.real(lhs);
        let rhs = self.subs.real(rhs);
        match (lhs.as_var(), rhs.as_var()) {
            (_, Some(_)) => {
                self.subs
                    .union(rhs, lhs)
                    .map_err(|(v, t)| TypeUnifyError::Occurs(v, t))?;
                Ok(())
            }
            (Some(_), _) => {
                self.subs
                    .union(lhs, rhs)
                    .map_err(|(v, t)| TypeUnifyError::Occurs(v, t))?;
                Ok(())
            }
            (None, None) => self.unify_inside(lhs, rhs),
        }
    }

    fn zip_unify(&mut self, lhs: &[Ty<'t>], rhs: &[Ty<'t>]) -> Result<(), TypeUnifyError<'t>> {
        if lhs.len() != rhs.len() {
            return Err(TypeUnifyError::Length(lhs.len(), rhs.len()));
        }
        for (&l, &r) in lhs.iter().zip(rhs) {
            self.try_unify(l, r)?;
        }
        Ok(())
    }

    /// Perform one level of equality testing between `lhs` and `rhs` and recursively call back
    /// into `self` for unification on any subterms.
    fn unify_inside(&mut self, lhs: Ty<'t>, rhs: Ty<'t>) -> Result<(), TypeUnifyError<'t>> {
        log::trace!("unify_inside {lhs} ~ {rhs}");
        match (*lhs.kind(), *rhs.kind()) {
            (lhs, rhs) if lhs == rhs => Ok(()),
            (TyKind::Arrow(l_arg, l_ret), TyKind::Arrow(r_arg, r_ret)) => {
                self.try_unify(l_arg, r_arg)?;
                self.try_unify(l_ret, r_ret)
            }
            (TyKind::App(l_h, l_args), TyKind::App(r_h, r_args)) => {
                let l_h = self.env.res.get(&l_h).ok_or(TypeUnifyError::Lookup(l_h))?;
                let r_h = self.env.res.get(&r_h).ok_or(TypeUnifyError::Lookup(r_h))?;
                self.try_unify(*l_h, *r_h)?;
                self.zip_unify(l_args, r_args)
            }
            (TyKind::Tuple(l_ts), TyKind::Tuple(r_ts)) => self.zip_unify(l_ts, r_ts),
            (TyKind::Vector(l), TyKind::Vector(r)) => self.try_unify(l, r),
            (_, _) => Err(TypeUnifyError::Mismatch(lhs, rhs)),
        }
    }

    pub fn canonicalize(&self, ct: Constraint<'t>) -> Vec<Constraint<'t>> {
        if ct.lhs == ct.rhs {
            // Discharge trivial equalities.
            Vec::new()
        } else {
            self.canonicalize_equal(ct.lhs, ct.rhs)
        }
    }

    fn canonicalize_equal(&self, lhs: Ty<'t>, rhs: Ty<'t>) -> Vec<Constraint<'t>> {
        match (*lhs.kind(), *rhs.kind()) {
            // Deconstruct arrows (and other matching type constructors).
            (TyKind::Arrow(l_arg, l_ret), TyKind::Arrow(r_arg, r_ret)) => self
                .canonicalize(Constraint::equal(l_arg, r_arg))
                .into_iter()
                .chain(self.canonicalize(Constraint::equal(l_ret, r_ret)))
                .collect(),
            (TyKind::App(l_h, l_args), TyKind::App(r_h, r_args))
                if l_args.len() == r_args.len() =>
            {
                std::iter::once(Constraint::equal(
                    // FIXME real span
                    Ty::path(self.ctxt, l_h, Span::dummy()),
                    Ty::path(self.ctxt, r_h, Span::dummy()),
                ))
                .chain(
                    l_args
                        .iter()
                        .zip(r_args)
                        .map(|(&l, &r)| Constraint::equal(l, r)),
                )
                .collect()
            }
            (TyKind::Tuple(l_ts), TyKind::Tuple(r_ts)) if l_ts.len() == r_ts.len() => l_ts
                .iter()
                .zip(r_ts)
                .map(|(&l, &r)| Constraint::equal(l, r))
                .collect(),
            // Orient vars before rigid vars.
            (TyKind::Var(_) | TyKind::Skolem(_), TyKind::Uni(_)) => {
                vec![Constraint::equal(rhs, lhs)]
            }
            // Lexicographically order type variables.
            (TyKind::Uni(a), TyKind::Uni(b)) if b.id < a.id => {
                vec![Constraint::equal(rhs, lhs)]
            }
            (TyKind::Var(a), TyKind::Var(b)) if b.name.sym < a.name.sym => {
                vec![Constraint::equal(rhs, lhs)]
            }
            (TyKind::Skolem(a), TyKind::Skolem(b)) if b.id < a.id => {
                vec![Constraint::equal(rhs, lhs)]
            }
            // Occurs check.
            (TyKind::Uni(a), _) if self.subs.occurs(a.id, rhs) => {
                vec![]
            }
            // Vars go first.
            (t, TyKind::Uni(_)) if !matches!(t, TyKind::Uni(_)) => {
                vec![Constraint::equal(rhs, lhs)]
            }
            (_, _) => vec![Constraint::equal(lhs, rhs)],
        }
    }

    fn interact(&self, this: Constraint<'t>, other: Constraint<'t>) -> Option<Constraint<'t>> {
        self.interact_equal(this.lhs, this.rhs, other.lhs, other.rhs)
    }

    fn interact_equal(
        &self,
        l1: Ty<'t>,
        r1: Ty<'t>,
        l2: Ty<'t>,
        r2: Ty<'t>,
    ) -> Option<Constraint<'t>> {
        Some(match (l1.kind(), l2.kind()) {
            (TyKind::Uni(a), TyKind::Uni(b)) if a == b => Constraint::equal(r1, r2),
            (TyKind::Skolem(a), TyKind::Skolem(b)) if a == b => Constraint::equal(r1, r2),
            (TyKind::Var(a), TyKind::Var(b)) if a.name.sym == b.name.sym => {
                Constraint::equal(r1, r2)
            }
            (TyKind::Uni(a), TyKind::Uni(_)) if self.subs.occurs(a.id, r2) => {
                //subs.insert(a.id, r1);
                //Constraint::equal(l2, subs.apply(r2))
                Constraint::equal(l2, r2.subst_uni_var(self.ctxt, *a, r1))
            }
            (_, _) => return None,
        })
    }
}

#[derive(Clone, Default)]
pub struct WorkList<'t> {
    contains: Set<Constraint<'t>>,
    queue: VecDeque<Constraint<'t>>,
}

impl<'t> WorkList<'t> {
    pub fn push(&mut self, ct: Constraint<'t>) {
        if self.contains.insert(ct) {
            self.queue.push_back(ct);
        }
    }

    pub fn pop(&mut self) -> Option<Constraint<'t>> {
        let front = self.queue.pop_front()?;
        self.contains.remove(&front);
        Some(front)
    }

    pub fn into_constraints(self) -> Vec<Constraint<'t>> {
        self.queue.into()
    }
}

impl<'t> Extend<Constraint<'t>> for WorkList<'t> {
    fn extend<I: IntoIterator<Item = Constraint<'t>>>(&mut self, iter: I) {
        for item in iter {
            self.push(item);
        }
    }
}

// Solving algorithm for flat constraints (adapted from GHC & OutsideIn).
//
// We maintain a worklist (`work_list`) of unprocessed constraints,
// and an "inert set" of constraints that have no pairwise interactions.
// Constraints in each are converted to "canonical" form.
//
// What does this mean? First, we start with canonical constraints.
//
// Canonical constraints
// ---------------------
// Given an equality constraint C = t1 ~ t2, we want to convert it to
// a simpler form.
//
// The canonicalization rules are:
//
// [REFL]    canonicalize(t ~ t) = []
// [CONS]    canonicalize(T t1..tn ~ S s1..sn) = [T ~ S, t1 ~ s1, .., tn ~ sn]
// [ORIENT]  canonicalize(t2 ~ t1) = [t1 ~ t2] if t1 < t2
//
// where t1 < t2 is defined by:
//              var1 < var2 if var1 < var2 lexicographically
//   unification var < rigid var
//               var < any other type
//
// Why have orientation? We want canonical equality constraints
// to have a particular "shape", namely, to prefer unifiable
// variables on the LHS of the equality. Unification variables are
// prefered before rigid variables in order to make the
// constraints seem more like a substitution.
//
// For other variable equalities, we order the variables lexicographically
// for termination reasons. Suppose we have the constraints
//
//   a ~ b, b ~ c, c ~ b (1).
//
// Using the rewrite/interaction rules below (namely EQ-DIFF), we could
// substitute [b := c] in a ~ b, resulting in
//
//   a ~ c, b ~ c, c ~ b.
//
// Applying the rule again with [c := b], we return to (1).
// Ordering variables lexicographically and limiting interactions
// to only canonicalized constraints, we would never have a situation
// where b ~ c and c ~ b could interact with a constraint such as a ~ b.
//
// In addition, we have an occurs check:
// [OCC-CHK] canonicalize(tv ~ t) = FAIL if tv in ftv(t), t != tv
//
// For example, suppose
//
//   a ~ [b], b ~ [a]
//
// reacts to (using EQ-DIFF)
//
//   a ~ [[a]], b ~ [a].
//
// Since OCC-CHK will fail to canonicalize the constraint a ~ [[a]],
// the EQ-DIFF interaction rule will not apply to it.
//
// We don't immediately bail out on a FAIL, but instead keep the
// offending constraints around and report them later.
//
// Interaction rules
// -----------------
// Given two *canonical* constraints, we want to transform them to make
// progress.
//
// [EQ-SAME] interact(tv ~ t1, tv ~ t2) = [tv ~ t1, t1 ~ t2]
//   (with the same variable on LHS, equate RHS)
// [EQ-DIFF] interact(tv1 ~ t1, tv2 ~ t2) = [tv1 ~ t1, tv2 ~ [tv1 := t1]t2]
//             if tv1 in ftv(t2)
//   (with different variables on LHS, substitute inside other RHS if
//    the variable is present)
//
// solve(Cs) :=
//   WL = canonicalize(Cs)
//   IS = {}
//
//   while !empty(WL):
//     ct := pop_front(WL)
//     reactions = []
//     for inert in IS:
//       reactions += canonicalize(interact(ct, inert))
//
//     if empty(reactions):
//       IS += canonicalize(ct)
//     else:
//       IS -= { inerts involved in reactions }
//       WL += reactions
//
//   for (t1 ~ t2) in IS:
//     unify(t1, t2)
//
//   return WL
//
impl<'t> Infer<'_, 't> {
    pub fn solve(&mut self) -> Result<Vec<Constraint<'t>>, TypeUnifyError<'t>> {
        // Constraints with no pairwise interactions.
        let mut inert_set = IndexSet::default();
        while let Some(ct) = self.constraints.pop() {
            let mut react_products = Vec::new();
            inert_set.retain(|&inert| {
                if let Some(rp) = self.interact(ct, inert) {
                    // If the constraint reacts with an inert, then
                    // both the (canonicalized) reaction product and the inert are
                    // put into the worklist (as the inert is no longer inert).
                    react_products.extend(self.canonicalize(rp));
                    react_products.push(inert);
                    false
                } else {
                    true
                }
            });

            if react_products.is_empty() {
                // No reactions, so the constraint is inert.
                inert_set.extend(self.canonicalize(ct));
            } else {
                // Otherwise, we have more work to do.
                self.constraints.extend(react_products);
            }
        }

        // We have no more possible reactions between constraints;
        // let's try to unify the inerts.
        for inert in &inert_set {
            self.try_unify(inert.lhs, inert.rhs)?;
        }

        // Residual constraints.
        Ok(self.constraints.clone().into_constraints())
    }
}
