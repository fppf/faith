/// The substitution data structure was adapted from [gluon](https://github.com/gluon-lang/gluon).
use std::{
    cell::{OnceCell, RefCell},
    fmt,
};

use base::{
    hash::Map,
    index::{Idx, IndexVec},
    pp::FormatIterator,
};
use hir::{Folder, HirCtxt, Substitutable, Visitor};

use crate::unify::{UnificationTable, UnifyKey, UnifyValue};

base::newtype_index! {
    #[derive(PartialOrd, Ord)]
    pub struct Level {}
}

base::newtype_index! {
    struct UnionByLevel {}
}

impl UnifyKey for UnionByLevel {
    type Value = Level;

    #[inline]
    fn order_roots(
        a: Self,
        a_value: &Self::Value,
        b: Self,
        b_value: &Self::Value,
    ) -> Option<(Self, Self)> {
        use std::cmp::Ordering;
        match a_value.cmp(b_value) {
            Ordering::Less => Some((a, b)),
            Ordering::Greater => Some((b, a)),
            Ordering::Equal => None,
        }
    }
}

impl UnifyValue for Level {
    type Error = !;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, Self::Error> {
        Ok(*lhs.min(rhs))
    }
}

pub struct Substitution<'hir, T: Substitutable<'hir>> {
    inner: RefCell<SubstitutionInner<'hir, T>>,
    pub ctxt: &'hir HirCtxt<'hir>,
}

struct SubstitutionInner<'hir, T: Substitutable<'hir>> {
    /// Stores the relationships of all variables in the substitution.
    union: UnificationTable<UnionByLevel>,
    /// Unification variables in the substitution, which can have a type
    /// written to them at most once.
    variables: IndexVec<T::Var, T>,
    types: Map<T::Var, OnceCell<T>>,
}

impl<'hir, T: Substitutable<'hir>> fmt::Display for Substitution<'hir, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.inner
                .borrow()
                .variables
                .iter_enumerated()
                .map(|(v, _)| {
                    self.find(v)
                        .map(|t| format!("{v} := {t}"))
                        .unwrap_or(format!("{v} := ?"))
                })
                .format(", ")
        )
    }
}

impl<'hir, T: Substitutable<'hir>> Substitution<'hir, T> {
    pub fn new(ctxt: &'hir HirCtxt<'hir>) -> Self {
        Self {
            inner: RefCell::new(SubstitutionInner {
                union: UnificationTable::default(),
                variables: IndexVec::default(),
                types: Map::default(),
            }),
            ctxt,
        }
    }

    pub fn new_var(&self) -> (T::Var, T) {
        let mut inner = self.inner.borrow_mut();
        let len = inner.variables.len();
        let var = inner
            .variables
            .push(T::make_var(self.ctxt, T::Var::new(len)));
        inner.types.insert(var, OnceCell::new());
        let key = inner.union.new_key(Level::new(var.index()));
        assert_eq!(var.index(), key.index());
        (var, inner.variables[var])
    }

    pub fn insert(&self, var: T::Var, t: T) {
        let mut inner = self.inner.borrow_mut();
        let index = inner.union.find(UnionByLevel::new(var.index())).index();
        let var = T::Var::new(index);
        match inner.types.get(&var) {
            Some(slot) => match slot.set(t) {
                Ok(()) => (),
                Err(_) => panic!("overwrote {} with {t}", slot.get().unwrap()),
            },
            None => unreachable!(),
        }
    }

    pub fn find(&self, var: T::Var) -> Option<T> {
        let mut inner = self.inner.borrow_mut();
        if var.index() >= inner.union.len() {
            return None;
        }
        let var_lvl = UnionByLevel::new(var.index());
        let index = inner.union.find(var_lvl).index();
        let repr_var = T::Var::new(index);
        inner
            .types
            .get(&repr_var)
            .and_then(|slot| slot.get().copied())
            .or_else(|| {
                if index == var.index() {
                    None
                } else {
                    Some(inner.variables[repr_var])
                }
            })
    }

    pub fn real(&self, t: T) -> T {
        t.as_var().and_then(|v| self.find(v)).unwrap_or(t)
    }

    /// Update the substitution so that `var` has the same type as `t`.
    pub fn union(&self, var: T, t: T) -> Result<(), (T::Var, T)> {
        let var = var.as_var().expect("var is not a variable");
        if let Some(other) = t.as_var() {
            // If t is another var, union them by level.
            self.inner
                .borrow_mut()
                .union
                .unify_var_var(
                    UnionByLevel::new(var.index()),
                    UnionByLevel::new(other.index()),
                )
                .expect("ICE (union)");
        } else {
            // If t is not a variable, insert it into the substitution,
            // provided var does not occur in t.
            if self.occurs(var, t) {
                return Err((var, t));
            }
            self.insert(var, t);
        }
        Ok(())
    }

    fn apply_once(&self, t: T) -> T {
        struct Applier<'a, 'hir, T: Substitutable<'hir>> {
            subs: &'a Substitution<'hir, T>,
        }

        impl<'hir, T: Substitutable<'hir>> Folder<'hir, T> for Applier<'_, 'hir, T> {
            fn ctxt(&self) -> &'hir HirCtxt<'hir> {
                self.subs.ctxt
            }

            fn fold(&mut self, t: T) -> T {
                if t.as_var().is_some() {
                    self.subs.real(t)
                } else {
                    t.fold_with(self)
                }
            }
        }

        Applier { subs: self }.fold(t)
    }

    pub fn apply(&self, mut t: T) -> T {
        // Apply substitution to fixed point.
        loop {
            let old = t;
            let new = self.apply_once(t);
            t = new;
            if new == old {
                return t;
            }
        }
    }

    pub fn occurs(&self, var: T::Var, t: T) -> bool {
        struct Occurs<'a, 'hir, T: Substitutable<'hir>> {
            occurs: bool,
            var: T::Var,
            subs: &'a Substitution<'hir, T>,
        }

        impl<'hir, T: Substitutable<'hir>> Visitor<T> for Occurs<'_, 'hir, T> {
            fn visit(&mut self, mut t: T) {
                if let Some(other) = t.as_var() {
                    if let Some(real) = self.subs.find(other) {
                        t = real;
                    } else {
                        if self.var == other {
                            self.occurs = true;
                            t.visit_with(self);
                            return;
                        }
                        // NB. This makes occur-check side-effecting.
                        self.subs.update_level(self.var, other);
                    }
                }
                t.visit_with(self);
            }
        }

        let mut occurs = Occurs {
            occurs: false,
            var,
            subs: self,
        };
        occurs.visit(t);
        occurs.occurs
    }

    fn update_level(&self, var: T::Var, other: T::Var) {
        let mut inner = self.inner.borrow_mut();
        let other_level = UnionByLevel::new(other.index());
        let level = inner
            .union
            .probe_value(UnionByLevel::new(var.index()))
            .min(inner.union.probe_value(other_level));
        inner
            .union
            .unify_var_value(other_level, level)
            .expect("ICE (update_level)");
    }
}
