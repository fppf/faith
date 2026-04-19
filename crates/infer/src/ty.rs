use std::{
    cell::{Cell, RefCell},
    fmt,
    hash::Hash,
};

use base::{
    arena::Interned,
    hash::{IndexMap, IndexSet, Map, Set},
    pp::FormatIterator,
};
use span::Ident;

use crate::{Res, ResId, Var};

pub use syntax::ast::BaseType;

base::declare_arena!('t, []);

pub struct TyCtxt<'t> {
    pub arena: &'t Arena<'t>,
    pub adts: RefCell<Map<Res, Adt<'t>>>,
    pub cons_to_adt: RefCell<Map<Res, Res>>,
    pub last_res_id: Cell<ResId>,
}

impl<'t> TyCtxt<'t> {
    pub fn new(arena: &'t Arena<'t>) -> Self {
        Self {
            arena,
            adts: RefCell::default(),
            cons_to_adt: RefCell::default(),
            last_res_id: Cell::new(ResId::ZERO + 1),
        }
    }

    pub fn new_res_id(&self) -> ResId {
        let next = self.last_res_id.get() + 1;
        self.last_res_id.replace(next);
        next
    }

    pub fn add_adt(&self, res: Res, adt: Adt<'t>) {
        let mut adts = self.adts.borrow_mut();
        let mut cons_to_adt = self.cons_to_adt.borrow_mut();
        for cons_res in adt.constructors.keys() {
            cons_to_adt.insert(*cons_res, res);
        }
        adts.insert(res, adt);
    }

    pub fn get_adt(&self, res: Res) -> Option<Adt<'t>> {
        // FIXME(perf)
        let adts = self.adts.borrow();
        adts.get(&res).cloned()
    }

    pub fn get_constructor(&self, cons_res: Res) -> Option<Constructor<'t>> {
        let cons_to_adt = self.cons_to_adt.borrow();
        let adt_res = cons_to_adt.get(&cons_res)?;
        self.adts
            .borrow()
            .get(&adt_res)
            .and_then(|adt| adt.constructors.get(&cons_res))
            .copied()
    }
}

#[derive(Clone, Debug)]
pub struct Adt<'t> {
    pub id: Ident,
    pub constructors: IndexMap<Res, Constructor<'t>>,
}

#[derive(Clone, Copy, Debug)]
pub struct Constructor<'t> {
    pub var: Var<'t>,
    pub args: &'t [Ty<'t>],
    pub index: usize,
    pub arity: usize,
    pub adt: Res,
}

/// A representation of a type during type inference.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Ty<'t>(Interned<'t, TyKind<'t>>);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TyKind<'t> {
    /// A base/builtin type.
    Base(BaseType),

    /// A user-defined type.
    User(Ident, Res),

    /// Represents a unification type variable.
    /// For a successfully inferred program, these should all be substituted away.
    Uni(UniVar),
    /// Represents a type variable that comes from a user-specified
    /// type, such as the `'a` in `'a -> 'a`.
    Var(TypeVar),
    /// Skolem/rigid type variable.
    Skolem(Skolem),

    /// Type with arguments.
    App(Ty<'t>, &'t [Ty<'t>]),

    /// Arrow type `a -> b`.
    Arrow(Ty<'t>, Ty<'t>),
    /// Product of types.
    Tuple(&'t [Ty<'t>]),
    /// Homogeneous vector.
    Vector(Ty<'t>),
}

base::newtype_index! {
    /// Unification variable generated during inference.
    pub struct UniVarId {}
}

impl fmt::Display for UniVarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{}", self.index())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct UniVar {
    pub id: UniVarId,
    pub kind: Kind,
}

impl UniVar {
    pub fn new(id: UniVarId, kind: Kind) -> Self {
        Self { id, kind }
    }
}

impl fmt::Display for UniVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}

/// A type variable coming from a user-written polymorphic type.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TypeVar {
    pub name: Ident,
}

impl TypeVar {
    pub fn new(name: Ident) -> Self {
        Self { name }
    }
}

impl fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)
    }
}

base::newtype_index! {
    /// Unique identifier for a skolem type variable.
    pub struct SkolemId {}
}

/// A skolem (or "rigid") type variable.
#[derive(Clone, Copy, Eq, Debug)]
pub struct Skolem {
    pub id: SkolemId,
    pub name: Ident,
}

impl Skolem {
    pub fn new(id: SkolemId, name: Ident) -> Self {
        Self { id, name }
    }
}

impl PartialEq for Skolem {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl fmt::Display for Skolem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}:{}", self.name, self.id.index())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Kind {
    /// Kind of term types is arity(0) = *.
    /// Constructor kinds are arity(1) = * -> *, ...
    arity: usize,
}

impl Kind {
    pub fn new(arity: usize) -> Self {
        Kind { arity }
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "*".fmt(f)?;
        for _ in 1..self.arity {
            " -> *".fmt(f)?;
        }
        Ok(())
    }
}

pub trait TypeVisitor<'t>: Sized {
    fn visit(&mut self, ty: Ty<'t>);
}

pub trait TypeFolder<'t>: Sized {
    fn ctxt(&self) -> &'t TyCtxt<'t>;

    fn fold(&mut self, ty: Ty<'t>) -> Ty<'t>;
}

impl<'t> Ty<'t> {
    #[inline]
    pub fn new(ctxt: &'t TyCtxt<'t>, kind: TyKind<'t>) -> Ty<'t> {
        Ty(Interned::new_unchecked(ctxt.arena.alloc(kind)))
    }

    #[inline]
    pub fn kind(self) -> &'t TyKind<'t> {
        (self.0).0
    }

    pub fn as_var(self) -> Option<UniVarId> {
        match self.kind() {
            TyKind::Uni(var) => Some(var.id),
            _ => None,
        }
    }

    pub fn as_user(self) -> Option<Res> {
        match self.kind() {
            TyKind::User(_, res) => Some(*res),
            TyKind::App(ty, _) => ty.as_user(),
            _ => None,
        }
    }

    pub fn visit_with<V>(self, v: &mut V)
    where
        V: TypeVisitor<'t>,
    {
        match *self.kind() {
            TyKind::Base(_)
            | TyKind::User(..)
            | TyKind::Var(_)
            | TyKind::Uni(_)
            | TyKind::Skolem(_) => (),
            TyKind::Vector(t) => v.visit(t),
            TyKind::Arrow(t1, t2) => {
                v.visit(t1);
                v.visit(t2);
            }
            TyKind::App(t, ts) => {
                v.visit(t);
                ts.iter().for_each(|&t| v.visit(t));
            }
            TyKind::Tuple(ts) => ts.iter().for_each(|&t| v.visit(t)),
        }
    }

    pub fn fold_with<F>(self, f: &mut F) -> Self
    where
        F: TypeFolder<'t>,
    {
        let kind = match *self.kind() {
            TyKind::Base(_)
            | TyKind::User(..)
            | TyKind::Var(_)
            | TyKind::Uni(_)
            | TyKind::Skolem(_) => return self,
            TyKind::App(h, ts) => TyKind::App(
                f.fold(h),
                f.ctxt()
                    .arena
                    .alloc_from_iter(ts.iter().map(|&t| f.fold(t))),
            ),
            TyKind::Vector(t) => TyKind::Vector(f.fold(t)),
            TyKind::Arrow(t1, t2) => TyKind::Arrow(f.fold(t1), f.fold(t2)),
            TyKind::Tuple(ts) => TyKind::Tuple(
                f.ctxt()
                    .arena
                    .alloc_from_iter(ts.iter().map(|&t| f.fold(t))),
            ),
        };
        if *self.kind() == kind {
            self
        } else {
            Ty::new(f.ctxt(), kind)
        }
    }

    pub fn tuple<I>(ctxt: &'t TyCtxt<'t>, iter: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        Ty::new(ctxt, TyKind::Tuple(ctxt.arena.alloc_from_iter(iter)))
    }

    pub fn app<I>(ctxt: &'t TyCtxt<'t>, head: Ty<'t>, args: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        Ty::new(ctxt, TyKind::App(head, ctxt.arena.alloc_from_iter(args)))
    }

    pub fn arrow(ctxt: &'t TyCtxt<'t>, source: Self, target: Self) -> Self {
        Ty::new(ctxt, TyKind::Arrow(source, target))
    }

    pub fn n_arrow<I>(ctxt: &'t TyCtxt<'t>, sources: I, target: Self) -> Self
    where
        I: IntoIterator<Item = Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        sources
            .into_iter()
            .rev()
            .fold(target, |acc, source| Ty::arrow(ctxt, source, acc))
    }

    pub fn type_var(ctxt: &'t TyCtxt<'t>, var: TypeVar) -> Self {
        Ty::new(ctxt, TyKind::Var(var))
    }

    pub fn uni_var(ctxt: &'t TyCtxt<'t>, var: UniVar) -> Self {
        Ty::new(ctxt, TyKind::Uni(var))
    }

    pub fn uni_vars(self) -> IndexSet<UniVar> {
        #[derive(Default)]
        struct Vars {
            acc: IndexSet<UniVar>,
        }

        impl<'t> TypeVisitor<'t> for Vars {
            fn visit(&mut self, ty: Ty<'t>) {
                if let TyKind::Uni(var) = ty.kind() {
                    self.acc.insert(*var);
                }
                ty.visit_with(self);
            }
        }

        let mut vars = Vars::default();
        vars.visit(self);
        vars.acc
    }

    pub fn type_vars(self) -> Set<TypeVar> {
        #[derive(Default)]
        struct Vars {
            acc: Set<TypeVar>,
        }

        impl<'t> TypeVisitor<'t> for Vars {
            fn visit(&mut self, ty: Ty<'t>) {
                if let TyKind::Var(var) = ty.kind() {
                    self.acc.insert(*var);
                }
                ty.visit_with(self);
            }
        }

        let mut vars = Vars::default();
        vars.visit(self);
        vars.acc
    }

    pub fn subst_uni_var(self, ctxt: &'t TyCtxt<'t>, var: UniVar, ty: Self) -> Self {
        struct Subs<'t> {
            ctxt: &'t TyCtxt<'t>,
            var: UniVar,
            ty: Ty<'t>,
        }

        impl<'t> TypeFolder<'t> for Subs<'t> {
            fn ctxt(&self) -> &'t TyCtxt<'t> {
                self.ctxt
            }

            fn fold(&mut self, ty: Ty<'t>) -> Ty<'t> {
                if let TyKind::Uni(var) = ty.kind()
                    && var.id == self.var.id
                {
                    self.ty
                } else {
                    ty.fold_with(self)
                }
            }
        }

        Subs { ctxt, var, ty }.fold(self)
    }
}

impl fmt::Display for Ty<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            TyKind::Base(b) => b.fmt(f),
            TyKind::User(id, _res) => id.fmt(f),
            TyKind::Uni(u) => u.fmt(f),
            TyKind::Var(v) => v.fmt(f),
            TyKind::Skolem(s) => s.fmt(f),
            TyKind::App(t, ts) => write!(f, "({t} {})", ts.iter().format(" ")),
            TyKind::Arrow(t1, t2) => write!(f, "({t1} -> {t2})"),
            TyKind::Tuple(ts) => write!(f, "({})", ts.iter().format(", ")),
            TyKind::Vector(t) => write!(f, "[{t}]"),
        }
    }
}
