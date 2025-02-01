use span::{Ident, SourceId, Sp, Span, Sym};

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Path<'ast> {
    pub root: Ident,
    pub access: &'ast [Ident],
    pub span: Span,
}

impl<'ast> Path<'ast> {
    pub fn new(root: Ident, access: &'ast [Ident], span: Span) -> Self {
        Self { root, access, span }
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn as_ident(&self) -> Option<Ident> {
        if self.access.is_empty() {
            Some(self.root)
        } else {
            None
        }
    }

    pub fn leaf(&self) -> Ident {
        if let Some(last) = self.access.last() {
            *last
        } else {
            self.root
        }
    }

    pub fn segments(&self) -> impl Iterator<Item = Ident> + '_ {
        std::iter::once(self.root).chain(self.access.iter().copied())
    }
}

/// The `main` expression is the entry point to the program.
#[derive(Clone, Copy, Debug)]
pub struct Program<'ast> {
    pub unit: &'ast CompUnit<'ast>,
    pub main: &'ast Sp<Expr<'ast>>,
}

/// A compilation unit, originating from a source file (`source_id`).
#[derive(Clone, Copy, Debug)]
pub struct CompUnit<'ast> {
    pub source_id: SourceId,
    pub items: &'ast [Sp<Item<'ast>>],
}

#[derive(Clone, Copy, Debug)]
pub enum BaseType {
    Unit,
    Bool,
    Str,
    Int32,
}

#[derive(Clone, Copy, Debug)]
pub enum Type<'ast> {
    /// (), bool, str, i32, ...
    Base(BaseType),
    /// 'a, 'b, ...
    Var(Ident),
    /// t1 -> t2
    Arrow(&'ast Sp<Type<'ast>>, &'ast Sp<Type<'ast>>),
    /// (t1, ..., tn)
    Tuple(&'ast [Sp<Type<'ast>>]),
    /// \[t\]
    Vector(&'ast Sp<Type<'ast>>),
    /// { l1 : t1, .., ln : tn }
    /// { l1 : t1, .., ln : tn | r }
    Row(
        &'ast [(Ident, Sp<Type<'ast>>)],
        Option<&'ast Sp<Type<'ast>>>,
    ),
    /// t, m.t, m.n.t, ...
    Path(Path<'ast>),
    /// p t1 .. tn
    App(Path<'ast>, &'ast [Sp<Type<'ast>>]),
}

#[derive(Clone, Copy, Debug)]
pub struct TypeDecl<'ast> {
    pub id: Ident,
    pub vars: &'ast [Ident],
    pub kind: TypeDeclKind<'ast>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub enum TypeDeclKind<'ast> {
    Alias(&'ast Sp<Type<'ast>>),
    Variant(&'ast [(Ident, &'ast [Sp<Type<'ast>>])]),
}

#[derive(Clone, Copy, Debug)]
pub enum Item<'ast> {
    Type(&'ast [TypeDecl<'ast>]),
    Val(Ident, Option<&'ast Sp<Type<'ast>>>, &'ast Sp<Expr<'ast>>),
    Mod(Ident, &'ast Sp<ModExpr<'ast>>),
    External(Ident, &'ast Sp<Type<'ast>>, Ident),
}

#[derive(Clone, Copy, Debug)]
pub enum ModExpr<'ast> {
    Path(Path<'ast>),
    Struct(&'ast [Sp<Item<'ast>>]),
    Import(Ident),
}

#[derive(Clone, Copy, Debug)]
pub enum Expr<'ast> {
    Path(Path<'ast>),
    Constructor(Path<'ast>),
    Lit(Lit),
    Ann(&'ast Sp<Expr<'ast>>, &'ast Sp<Type<'ast>>),
    Tuple(&'ast [Sp<Expr<'ast>>]),
    Vector(&'ast [Sp<Expr<'ast>>]),
    Case(
        &'ast Sp<Expr<'ast>>,
        &'ast [(Sp<Pat<'ast>>, Sp<Expr<'ast>>)],
    ),
    If(
        &'ast Sp<Expr<'ast>>,
        &'ast Sp<Expr<'ast>>,
        &'ast Sp<Expr<'ast>>,
    ),
    Lambda(Lambda<'ast>),
    App(&'ast Sp<Expr<'ast>>, &'ast [Sp<ExprArg<'ast>>]),
    Let(
        &'ast [(Sp<Pat<'ast>>, Sp<Expr<'ast>>)],
        &'ast Sp<Expr<'ast>>,
    ),
    Seq(&'ast Sp<Expr<'ast>>, &'ast Sp<Expr<'ast>>),
}

#[derive(Clone, Copy, Debug)]
pub enum ExprArg<'ast> {
    Expr(Sp<Expr<'ast>>),
    Type(Sp<Type<'ast>>),
}

#[derive(Clone, Copy, Debug)]
pub struct Lambda<'ast> {
    pub args: &'ast [Sp<Pat<'ast>>],
    pub body: &'ast Sp<Expr<'ast>>,
}

#[derive(Clone, Copy, Debug)]
pub enum Pat<'ast> {
    Wild,
    Lit(Lit),
    Var(Ident),
    Ann(&'ast Sp<Pat<'ast>>, &'ast Sp<Type<'ast>>),
    Tuple(&'ast [Sp<Pat<'ast>>]),
    Constructor(Path<'ast>, &'ast [Sp<Pat<'ast>>]),
    Or(&'ast [Sp<Pat<'ast>>]),
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Lit {
    Unit,
    Bool(bool),
    Int32(Sym),
    Str(Sym),
}
