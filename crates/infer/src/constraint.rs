use std::{fmt, hash::Hash, marker::PhantomData};

use base::hash::IndexSet;
use hir::*;

use crate::{TypeChecker, error::TypeUnifyError, substitution::Substitution};

pub fn solve<'a, T, U>(
    unifier: &mut U,
    constraints: Vec<Constraint<'a, T>>,
) -> Result<Vec<Constraint<'a, T>>, U::Error>
where
    T: Constrainable<'a>,
    U: Unifier<'a, T>,
{
    let mut solver = Solver::default();
    solver.work_list.extend(
        constraints
            .iter()
            .flat_map(|&constraint| T::canonicalize(unifier.subs(), constraint)),
    );
    solver.solve(unifier)
}

/// Equality constraint (t1 ~ t2).
///
/// Why all the generics? Really, we can just specialize to Type<'hir>.
/// I originally also wanted to reuse all this for kind inference, but
/// I ended up going with a simpler kind system that doesn't require it.
/// Anyways, I think making it a little abstract helps with keeping the
/// logic clean (debatable, but eh). Could degenerify it later.
#[derive(Clone, Copy, PartialEq, Hash, Debug)]
pub struct Constraint<'hir, T> {
    pub lhs: T,
    pub rhs: T,
    _marker: PhantomData<&'hir ()>,
}

pub trait Constrainable<'hir>: std::hash::Hash + Substitutable<'hir> {
    fn canonicalize(
        subs: &Substitution<'hir, Self>,
        ct: Constraint<'hir, Self>,
    ) -> Vec<Constraint<'hir, Self>> {
        if ct.lhs == ct.rhs {
            // Discharge trivial equalities.
            Vec::new()
        } else {
            Self::canonicalize_equal(subs, ct.lhs, ct.rhs)
        }
    }

    fn canonicalize_equal(
        subs: &Substitution<'hir, Self>,
        lhs: Self,
        rhs: Self,
    ) -> Vec<Constraint<'hir, Self>>;

    fn interact(
        subs: &Substitution<'hir, Self>,
        this: Constraint<'hir, Self>,
        other: Constraint<'hir, Self>,
    ) -> Option<Constraint<'hir, Self>> {
        Self::interact_equal(subs, this.lhs, this.rhs, other.lhs, other.rhs)
    }

    fn interact_equal(
        subs: &Substitution<'hir, Self>,
        l1: Self,
        r1: Self,
        l2: Self,
        r2: Self,
    ) -> Option<Constraint<'hir, Self>>;
}

impl<'hir, T> Eq for Constraint<'hir, T> where T: Constrainable<'hir> {}
/*
impl<'hir, T> PartialEq for Constraint<'hir, T>
where
    T: Constrainable<'hir>,
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


impl<'hir, T> Hash for Constraint<'hir, T> where T:Constrainable<'hir> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {

    }
}
*/

impl<'hir, T> fmt::Display for Constraint<'hir, T>
where
    T: Constrainable<'hir>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ~ {}", self.lhs, self.rhs)
    }
}

impl<'hir, T> Constraint<'hir, T>
where
    T: Constrainable<'hir>,
{
    #[inline]
    pub fn equal(lhs: T, rhs: T) -> Self {
        Self {
            lhs,
            rhs,
            _marker: PhantomData,
        }
    }
}

pub trait UnifyError<'a, T: Substitutable<'a>> {
    fn length(lhs: usize, rhs: usize) -> Self;
    fn occurs(var: T::Var, t: T) -> Self;
}

pub trait Unifier<'a, T>
where
    T: Constrainable<'a>,
{
    type Error: UnifyError<'a, T>;

    fn subs(&self) -> &Substitution<'a, T>;

    fn try_unify(&mut self, lhs: T, rhs: T) -> Result<(), Self::Error> {
        let lhs = self.subs().real(lhs);
        let rhs = self.subs().real(rhs);
        match (lhs.as_var(), rhs.as_var()) {
            (_, Some(_)) => {
                self.subs()
                    .union(rhs, lhs)
                    .map_err(|(v, t)| Self::Error::occurs(v, t))?;
                Ok(())
            }
            (Some(_), _) => {
                self.subs()
                    .union(lhs, rhs)
                    .map_err(|(v, t)| Self::Error::occurs(v, t))?;
                Ok(())
            }
            (None, None) => self.unify_inside(lhs, rhs),
        }
    }

    fn zip_unify(&mut self, lhs: &[T], rhs: &[T]) -> Result<(), Self::Error> {
        if lhs.len() != rhs.len() {
            return Err(Self::Error::length(lhs.len(), rhs.len()));
        }

        for (&l, &r) in lhs.iter().zip(rhs) {
            self.try_unify(l, r)?;
        }

        Ok(())
    }

    /// Perform one level of equality testing between `lhs` and `rhs` and recursively call back
    /// into `self` for unification on any subterms.
    fn unify_inside(&mut self, lhs: T, rhs: T) -> Result<(), Self::Error>;
}

mod wl {
    use super::Constraint;
    use base::hash::Set;
    use std::collections::VecDeque;

    use super::Constrainable;

    pub struct WorkList<'a, T> {
        contains: Set<Constraint<'a, T>>,
        queue: VecDeque<Constraint<'a, T>>,
    }

    impl<T> Default for WorkList<'_, T> {
        fn default() -> Self {
            Self {
                contains: Set::default(),
                queue: VecDeque::default(),
            }
        }
    }

    impl<'a, T> WorkList<'a, T>
    where
        T: Constrainable<'a>,
    {
        pub fn push(&mut self, ct: Constraint<'a, T>) {
            if self.contains.insert(ct) {
                self.queue.push_back(ct);
            }
        }

        pub fn pop(&mut self) -> Option<Constraint<'a, T>> {
            let front = self.queue.pop_front()?;
            self.contains.remove(&front);
            Some(front)
        }

        pub fn into_constraints(self) -> Vec<Constraint<'a, T>> {
            self.queue.into()
        }
    }

    impl<'a, T> Extend<Constraint<'a, T>> for WorkList<'a, T>
    where
        T: Constrainable<'a>,
    {
        fn extend<I: IntoIterator<Item = Constraint<'a, T>>>(&mut self, iter: I) {
            for item in iter {
                self.push(item);
            }
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

struct Solver<'a, T> {
    /// Constraints with no pairwise interactions.
    inert_set: IndexSet<Constraint<'a, T>>,

    /// Unprocessed constraints.
    work_list: wl::WorkList<'a, T>,
}

impl<T> Default for Solver<'_, T> {
    fn default() -> Self {
        Self {
            inert_set: IndexSet::default(),
            work_list: wl::WorkList::default(),
        }
    }
}

impl<'a, T> Solver<'a, T>
where
    T: Constrainable<'a>,
{
    fn solve<U>(mut self, unifier: &mut U) -> Result<Vec<Constraint<'a, T>>, U::Error>
    where
        U: Unifier<'a, T>,
    {
        while self.step(unifier.subs()) {
            // step
        }

        // We have no more possible reactions between constraints;
        // let's try to unify the inerts.
        for inert in &self.inert_set {
            unifier.try_unify(inert.lhs, inert.rhs)?;
        }

        // Residual constraints.
        Ok(self.work_list.into_constraints())
    }

    fn step(&mut self, subs: &Substitution<'a, T>) -> bool {
        if let Some(ct) = self.work_list.pop() {
            let mut react_products = Vec::new();

            self.inert_set.retain(|&inert| {
                if let Some(rp) = T::interact(subs, ct, inert) {
                    // If the constraint reacts with an inert, then
                    // both the (canonicalized) reaction product and the inert are
                    // put into the worklist (as the inert is no longer inert).
                    react_products.extend(T::canonicalize(subs, rp));
                    react_products.push(inert);
                    false
                } else {
                    true
                }
            });

            if react_products.is_empty() {
                // No reactions, so the constraint is inert.
                self.inert_set.extend(T::canonicalize(subs, ct));
            } else {
                // Otherwise, we have more work to do.
                self.work_list.extend(react_products);
            }

            true
        } else {
            // Worklist is empty, we are done.
            false
        }
    }
}

impl<'hir> Unifier<'hir, Ty<'hir>> for TypeChecker<'hir> {
    type Error = TypeUnifyError<'hir>;

    fn subs(&self) -> &Substitution<'hir, Ty<'hir>> {
        &self.subs
    }

    fn unify_inside(&mut self, lhs: Ty<'hir>, rhs: Ty<'hir>) -> Result<(), Self::Error> {
        log::trace!("unify_inside {lhs} ~ {rhs}");
        match (*lhs.kind(), *rhs.kind()) {
            (lhs, rhs) if lhs == rhs => Ok(()),
            (TyKind::Arrow(l_u, l_arg, l_ret), TyKind::Arrow(r_u, r_arg, r_ret)) => {
                self.webs.unify_var_var(l_u, r_u).unwrap();
                self.try_unify(l_arg, r_arg)?;
                self.try_unify(l_ret, r_ret)
            }
            (TyKind::App(l_h, l_args), TyKind::App(r_h, r_args)) => {
                let l_h = self
                    .hir_ctxt
                    .get_type(l_h.res().hir_id())
                    .ok_or(TypeUnifyError::Lookup(l_h))?;
                let r_h = self
                    .hir_ctxt
                    .get_type(r_h.res().hir_id())
                    .ok_or(TypeUnifyError::Lookup(r_h))?;
                self.try_unify(l_h, r_h)?;
                self.zip_unify(l_args, r_args)
            }
            (TyKind::Tuple(l_ts), TyKind::Tuple(r_ts)) => self.zip_unify(l_ts, r_ts),
            (TyKind::Vector(l), TyKind::Vector(r)) => self.try_unify(l, r),
            (_, _) => Err(TypeUnifyError::Mismatch(lhs, rhs)),
        }
    }
}

impl<'hir> Constrainable<'hir> for Ty<'hir> {
    fn canonicalize_equal(
        subs: &Substitution<'hir, Ty<'hir>>,
        lhs: Ty<'hir>,
        rhs: Ty<'hir>,
    ) -> Vec<Constraint<'hir, Ty<'hir>>> {
        match (*lhs.kind(), *rhs.kind()) {
            // Deconstruct arrows (and other matching type constructors).
            (TyKind::Arrow(_, l_arg, l_ret), TyKind::Arrow(_, r_arg, r_ret)) => {
                Self::canonicalize(subs, Constraint::equal(l_arg, r_arg))
                    .into_iter()
                    .chain(Self::canonicalize(subs, Constraint::equal(l_ret, r_ret)))
                    .collect()
            }
            (TyKind::App(l_h, l_args), TyKind::App(r_h, r_args))
                if l_args.len() == r_args.len() =>
            {
                std::iter::once(Constraint::equal(
                    Ty::path(subs.ctxt, l_h),
                    Ty::path(subs.ctxt, r_h),
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
            (TyKind::Uni(a), _) if subs.occurs(a.id, rhs) => {
                vec![]
            }
            // Vars go first.
            (t, TyKind::Uni(_)) if !matches!(t, TyKind::Uni(_)) => {
                vec![Constraint::equal(rhs, lhs)]
            }
            (_, _) => vec![Constraint::equal(lhs, rhs)],
        }
    }

    fn interact_equal(
        subs: &Substitution<'hir, Ty<'hir>>,
        l1: Ty<'hir>,
        r1: Ty<'hir>,
        l2: Ty<'hir>,
        r2: Ty<'hir>,
    ) -> Option<Constraint<'hir, Ty<'hir>>> {
        Some(match (*l1.kind(), *l2.kind()) {
            (TyKind::Uni(a), TyKind::Uni(b)) if a == b => Constraint::equal(r1, r2),
            (TyKind::Skolem(a), TyKind::Skolem(b)) if a == b => Constraint::equal(r1, r2),
            (TyKind::Var(a), TyKind::Var(b)) if a.name.sym == b.name.sym => {
                Constraint::equal(r1, r2)
            }
            (TyKind::Uni(a), TyKind::Uni(_)) if subs.occurs(a.id, r2) => {
                //subs.insert(a.id, r1);
                //Constraint::equal(l2, subs.apply(r2))
                Constraint::equal(l2, r2.subst_uni_var(subs.ctxt, a, r1))
            }
            (_, _) => return None,
        })
    }
}
