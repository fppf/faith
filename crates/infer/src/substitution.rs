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
use hir::{Folder, Substitutable, Visitor};

use crate::{
    unify::{UnificationTable, UnifyKey, UnifyValue},
    Arena,
};

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

pub struct Substitution<'hir, T>
where
    T: Substitutable<'hir>,
{
    /// Stores the relationships of all variables in the substitution.
    union: RefCell<UnificationTable<UnionByLevel>>,
    /// Unification variables in the substitution, which can have a type
    /// written to them at most once.
    variables: RefCell<IndexVec<T::Var, T>>,
    types: RefCell<Map<T::Var, OnceCell<T>>>,
    pub arena: &'hir Arena<'hir>,
}

impl<'hir, T> fmt::Display for Substitution<'hir, T>
where
    T: Substitutable<'hir>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.variables
                .borrow()
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

impl<'hir, T> Substitution<'hir, T>
where
    T: Substitutable<'hir>,
{
    pub fn new(arena: &'hir Arena<'hir>) -> Self {
        Self {
            union: RefCell::default(),
            variables: RefCell::default(),
            types: RefCell::default(),
            arena,
        }
    }

    pub fn new_var(&self) -> (T::Var, T) {
        let len = self.variables.borrow().len();
        let var = self
            .variables
            .borrow_mut()
            .push(T::make_var(self.arena, T::Var::new(len)));
        self.types.borrow_mut().insert(var, OnceCell::new());
        let key = self.union.borrow_mut().new_key(Level::new(var.index()));
        assert_eq!(var.index(), key.index());
        (var, self.variables.borrow()[var])
    }

    pub fn insert(&self, var: T::Var, t: T) {
        let mut union = self.union.borrow_mut();
        let index = union.find(UnionByLevel::new(var.index())).index();
        let var = T::Var::new(index);
        match self.types.borrow().get(&var) {
            Some(slot) => match slot.set(t) {
                Ok(()) => (),
                Err(_) => panic!("overwrote {} with {t}", slot.get().unwrap()),
            },
            None => unreachable!(),
        }
    }

    #[allow(unused)]
    pub fn unioned(&self, var_a: T::Var, var_b: T::Var) -> bool {
        self.union.borrow_mut().unioned(
            UnionByLevel::new(var_a.index()),
            UnionByLevel::new(var_b.index()),
        )
    }

    pub fn find(&self, var: T::Var) -> Option<T> {
        let mut union = self.union.borrow_mut();
        if var.index() >= union.len() {
            return None;
        }
        let var_lvl = UnionByLevel::new(var.index());
        let index = union.find(var_lvl).index();
        let repr_var = T::Var::new(index);
        self.types
            .borrow()
            .get(&repr_var)
            .and_then(|slot| slot.get().copied())
            .or_else(|| {
                if index == var.index() {
                    None
                } else {
                    Some(self.variables.borrow()[repr_var])
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
            self.union
                .borrow_mut()
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
        struct Applier<'a, 'hir, T>
        where
            T: Substitutable<'hir>,
        {
            subs: &'a Substitution<'hir, T>,
        }

        impl<'hir, T> Folder<'hir, T> for Applier<'_, 'hir, T>
        where
            T: Substitutable<'hir>,
        {
            fn arena(&self) -> &'hir Arena<'hir> {
                self.subs.arena
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
        struct Occurs<'a, 'hir, T>
        where
            T: Substitutable<'hir>,
        {
            occurs: bool,
            var: T::Var,
            subs: &'a Substitution<'hir, T>,
        }

        impl<'hir, T> Visitor<T> for Occurs<'_, 'hir, T>
        where
            T: Substitutable<'hir>,
        {
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
        let mut union = self.union.borrow_mut();
        let other_level = UnionByLevel::new(other.index());
        let level = union
            .probe_value(UnionByLevel::new(var.index()))
            .min(union.probe_value(other_level));
        union
            .unify_var_value(other_level, level)
            .expect("ICE (update_level)");
    }
}
