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

use crate::{
    TyCtxt,
    typ::{Folder, Kind, Ty, UniVar, UniVarId, Visitor},
    unify::{UnificationTable, UnifyKey, UnifyValue},
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

pub struct Substitution<'t> {
    inner: RefCell<SubstitutionInner<'t>>,
    pub ctxt: &'t TyCtxt<'t>,
}

struct SubstitutionInner<'t> {
    /// Stores the relationships of all variables in the substitution.
    union: UnificationTable<UnionByLevel>,
    /// Unification variables in the substitution, which can have a type
    /// written to them at most once.
    variables: IndexVec<UniVarId, Ty<'t>>,
    types: Map<UniVarId, OnceCell<Ty<'t>>>,
}

impl fmt::Display for Substitution<'_> {
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

impl<'t> Substitution<'t> {
    pub fn new(ctxt: &'t TyCtxt<'t>) -> Self {
        Self {
            inner: RefCell::new(SubstitutionInner {
                union: UnificationTable::default(),
                variables: IndexVec::default(),
                types: Map::default(),
            }),
            ctxt,
        }
    }

    pub fn new_var(&self) -> (UniVarId, Ty<'t>) {
        let mut inner = self.inner.borrow_mut();
        let len = inner.variables.len();
        let var = inner.variables.push(Ty::uni_var(
            self.ctxt,
            UniVar::new(UniVarId::new(len), Kind::new(0)),
        ));
        inner.types.insert(var, OnceCell::new());
        let key = inner.union.new_key(Level::new(var.index()));
        assert_eq!(var.index(), key.index());
        (var, inner.variables[var])
    }

    pub fn insert(&self, var: UniVarId, ty: Ty<'t>) {
        let mut inner = self.inner.borrow_mut();
        let index = inner.union.find(UnionByLevel::new(var.index())).index();
        let var = UniVarId::new(index);
        match inner.types.get(&var) {
            Some(slot) => match slot.set(ty) {
                Ok(()) => (),
                Err(_) => panic!("overwrote {} with {ty}", slot.get().unwrap()),
            },
            None => unreachable!(),
        }
    }

    pub fn find(&self, var: UniVarId) -> Option<Ty<'t>> {
        let mut inner = self.inner.borrow_mut();
        if var.index() >= inner.union.len() {
            return None;
        }
        let var_lvl = UnionByLevel::new(var.index());
        let index = inner.union.find(var_lvl).index();
        let repr_var = UniVarId::new(index);
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

    pub fn real(&self, ty: Ty<'t>) -> Ty<'t> {
        ty.as_var().and_then(|v| self.find(v)).unwrap_or(ty)
    }

    /// Update the substitution so that `var` has the same type as `ty`.
    pub fn union(&self, var: Ty<'t>, ty: Ty<'t>) -> Result<(), (UniVarId, Ty<'t>)> {
        let var = var.as_var().expect("var is not a variable");
        if let Some(other) = ty.as_var() {
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
            if self.occurs(var, ty) {
                return Err((var, ty));
            }
            self.insert(var, ty);
        }
        Ok(())
    }

    fn apply_once(&self, ty: Ty<'t>) -> Ty<'t> {
        struct Applier<'a, 't> {
            subs: &'a Substitution<'t>,
        }

        impl<'t> Folder<'t, Ty<'t>> for Applier<'_, 't> {
            fn ctxt(&self) -> &'t TyCtxt<'t> {
                self.subs.ctxt
            }

            fn fold(&mut self, ty: Ty<'t>) -> Ty<'t> {
                if ty.as_var().is_some() {
                    self.subs.real(ty)
                } else {
                    ty.fold_with(self)
                }
            }
        }

        Applier { subs: self }.fold(ty)
    }

    pub fn apply(&self, mut ty: Ty<'t>) -> Ty<'t> {
        // Apply substitution to fixed point.
        loop {
            let old = ty;
            let new = self.apply_once(ty);
            ty = new;
            if new == old {
                return ty;
            }
        }
    }

    pub fn occurs(&self, var: UniVarId, ty: Ty<'t>) -> bool {
        struct Occurs<'a, 't> {
            occurs: bool,
            var: UniVarId,
            subs: &'a Substitution<'t>,
        }

        impl<'t> Visitor<Ty<'t>> for Occurs<'_, 't> {
            fn visit(&mut self, mut ty: Ty<'t>) {
                if let Some(other) = ty.as_var() {
                    if let Some(real) = self.subs.find(other) {
                        ty = real;
                    } else {
                        if self.var == other {
                            self.occurs = true;
                            ty.visit_with(self);
                            return;
                        }
                        // NB. This makes occur-check side-effecting.
                        self.subs.update_level(self.var, other);
                    }
                }
                ty.visit_with(self);
            }
        }

        let mut occurs = Occurs {
            occurs: false,
            var,
            subs: self,
        };
        occurs.visit(ty);
        occurs.occurs
    }

    fn update_level(&self, var: UniVarId, other: UniVarId) {
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
