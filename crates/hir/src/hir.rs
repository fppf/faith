use std::{
    fmt,
    ops::{Index, IndexMut},
};

use base::{
    arena::Interned,
    hash::{Map, Set},
};
use span::{Ident, SourceId, Sp, Span, Sym};

pub use crate::{path::*, typ::*, Arena};

base::newtype_index! {
    pub struct HirId {}
}

impl fmt::Display for HirId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.index())
    }
}

pub type HirMap<T> = Map<HirId, T>;
pub type HirSet = Set<HirId>;

base::newtype_index! {
    pub struct WebId {}
}

pub const NO_WEB: WebId = WebId::ZERO;

#[derive(Clone, Debug)]
pub struct Program<'hir> {
    pub imports: Map<SourceId, &'hir CompUnit<'hir>>,
    pub values: HirMap<Value<'hir>>,
    pub constructors: HirMap<Constructor<'hir>>,
    pub types: HirMap<TypeDecl<'hir>>,
    pub unit: &'hir CompUnit<'hir>,
    pub main: Expr<'hir>,
}

#[derive(Clone, Copy, Debug)]
pub struct CompUnit<'hir> {
    pub source_id: SourceId,
    pub items: &'hir Items<'hir>,
}

#[derive(Clone, Copy, Debug)]
pub struct Value<'hir> {
    pub hir_id: HirId,
    pub expr: Expr<'hir>,
    pub typ: Option<Ty<'hir>>,
}

#[derive(Clone, Copy, Debug)]
pub struct Constructor<'hir> {
    pub id: Ident,
    pub typ: Ty<'hir>,
    pub arity: usize,
    pub decl: HirId,
}

#[derive(Clone, Copy, Debug)]
pub struct TypeDecl<'hir> {
    pub id: Ident,
    pub vars: &'hir [TypeVar],
    pub kind: TypeDeclKind<'hir>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub enum TypeDeclKind<'hir> {
    Alias(Sp<Ty<'hir>>),
    Variant(&'hir Set<HirId>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Expr<'hir>(Interned<'hir, Sp<ExprKind<'hir>>>);

impl<'hir> Expr<'hir> {
    #[inline]
    pub fn new(arena: &'hir Arena<'hir>, kind: ExprKind<'hir>, span: Span) -> Self {
        Expr(Interned::new_unchecked(arena.alloc(Sp::new(kind, span))))
    }

    #[inline]
    pub fn kind(self) -> &'hir ExprKind<'hir> {
        (self.0).0
    }

    #[inline]
    pub fn span(self) -> Span {
        self.0.span
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ExprKind<'hir> {
    Path(Path<'hir>),
    Constructor(Path<'hir>),
    External(Sym),
    Lit(Lit),
    Ann(Expr<'hir>, Sp<Ty<'hir>>),
    Tuple(&'hir [Expr<'hir>]),
    Vector(&'hir [Expr<'hir>]),
    Lambda(Lambda<'hir>),
    App(WebId, Expr<'hir>, &'hir [ExprArg<'hir>]),
    Let(&'hir [LetBind<'hir>], Expr<'hir>),
    If(Expr<'hir>, Expr<'hir>, Expr<'hir>),
    Case(Expr<'hir>, &'hir [CaseArm<'hir>]),
    Seq(Expr<'hir>, Expr<'hir>),
}

pub type LetBind<'hir> = (Pat<'hir>, Expr<'hir>);
pub type CaseArm<'hir> = (Pat<'hir>, Expr<'hir>);

#[derive(Clone, Copy, Debug)]
pub enum ExprArg<'hir> {
    Expr(Expr<'hir>),
    Type(Ty<'hir>),
}

#[derive(Clone, Copy, Debug)]
pub struct Lambda<'hir> {
    pub web_id: WebId,
    pub args: &'hir [Pat<'hir>],
    pub body: Expr<'hir>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Pat<'hir> {
    pub kind: PatKind<'hir>,
    pub span: Span,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PatKind<'hir> {
    Wild,
    Var(Ident, HirId),
    Lit(Lit),
    Ann(&'hir Pat<'hir>, Sp<Ty<'hir>>),
    Tuple(&'hir [Pat<'hir>]),
    Constructor(Path<'hir>, &'hir [Pat<'hir>]),
    Or(&'hir [Pat<'hir>]),
}

impl<'hir> Pat<'hir> {
    pub fn fold_with<F>(&'hir self, f: &mut F) -> &'hir Pat<'hir>
    where
        F: Folder<'hir, &'hir Pat<'hir>>,
    {
        let kind = match self.kind {
            PatKind::Wild | PatKind::Var(..) | PatKind::Lit(_) => return self,
            PatKind::Ann(p, t) => PatKind::Ann(f.fold(p), t),
            PatKind::Tuple(ps) => {
                PatKind::Tuple(f.arena().alloc_from_iter(ps.iter().map(|p| *f.fold(p))))
            }
            PatKind::Constructor(id, ps) => {
                PatKind::Constructor(id, f.arena().alloc_from_iter(ps.iter().map(|p| *f.fold(p))))
            }
            PatKind::Or(ps) => {
                PatKind::Or(f.arena().alloc_from_iter(ps.iter().map(|p| *f.fold(p))))
            }
        };
        if self.kind == kind {
            self
        } else {
            f.arena().alloc(Pat {
                kind,
                span: self.span,
            })
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lit {
    Unit,
    Bool(bool),
    Int32(i32),
    Str(Sym),
}

#[derive(Clone, Copy, Debug)]
pub struct TypeDeclGroup<'hir> {
    pub decls: &'hir [TypeDecl<'hir>],
}

impl TypeDeclGroup<'_> {
    pub fn has_ident(&self, id: Ident) -> bool {
        self.decls.iter().any(|decl| decl.id == id)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ModExpr<'hir> {
    pub kind: ModExprKind<'hir>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub enum ModExprKind<'hir> {
    Path(Path<'hir>),
    Struct(&'hir Items<'hir>),
    Functor(Ident, &'hir ModType<'hir>, &'hir ModExpr<'hir>),
    App(&'hir ModExpr<'hir>, &'hir ModExpr<'hir>),
    Ann(&'hir ModExpr<'hir>, &'hir ModType<'hir>),
    Import(SourceId),
}

#[derive(Clone, Default, Debug)]
pub struct Items<'hir> {
    pub values: Map<Ident, Value<'hir>>,
    pub types: HirSet,
    pub modules: Map<Ident, &'hir ModExpr<'hir>>,

    pub type_groups: HirMap<HirSet>,
}

#[derive(Clone, Default, Debug)]
pub struct Specs<'hir> {
    pub values: Map<Ident, Ty<'hir>>,
    pub types: HirSet,
}

#[derive(Clone, Copy, Debug)]
pub struct ModType<'hir> {
    pub kind: ModTypeKind<'hir>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub enum ModTypeKind<'hir> {
    Path(Path<'hir>),
    Sig(&'hir Specs<'hir>),
    Arrow(Ident, &'hir ModType<'hir>, &'hir ModType<'hir>),
}
