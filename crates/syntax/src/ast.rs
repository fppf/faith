use std::fmt;

use base::hash::Map;
use span::{Ident, SourceId, Sp, Span, Sym};

base::newtype_index! {
    pub struct AstId {}
}

impl fmt::Display for AstId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.index())
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Path<'ast> {
    pub root: Ident,
    pub access: &'ast [Ident],
    pub span: Span,
    pub ast_id: AstId,
}

impl<'ast> Path<'ast> {
    pub fn new(root: Ident, access: &'ast [Ident], span: Span, ast_id: AstId) -> Self {
        Self {
            root,
            access,
            span,
            ast_id,
        }
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn as_ident(&self) -> Option<Id> {
        if self.access.is_empty() {
            Some(Id::new(self.root, self.ast_id))
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

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Id {
    pub ident: Ident,
    pub ast_id: AstId,
}

impl Id {
    pub fn new(ident: Ident, ast_id: AstId) -> Self {
        Self { ident, ast_id }
    }
}

/// The `main` expression is the entry point to the program.
#[derive(Clone, Debug)]
pub struct Program<'ast> {
    pub imports: Map<SourceId, &'ast CompUnit<'ast>>,
    pub unit: &'ast CompUnit<'ast>,
    pub main: &'ast Expr<'ast>,
}

/// A compilation unit, originating from a source file (`source_id`).
#[derive(Clone, Copy, Debug)]
pub struct CompUnit<'ast> {
    pub source_id: SourceId,
    pub items: &'ast [Sp<Item<'ast>>],
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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
    Var(Id),
    /// t1 -> t2
    Arrow(&'ast Sp<Type<'ast>>, &'ast Sp<Type<'ast>>),
    /// (t1, ..., tn)
    Tuple(&'ast [Sp<Type<'ast>>]),
    /// \[t\]
    Vector(&'ast Sp<Type<'ast>>),
    /// { l1 : t1, .., ln : tn }
    /// { l1 : t1, .., ln : tn | r }
    Row(&'ast [(Id, Sp<Type<'ast>>)], Option<&'ast Sp<Type<'ast>>>),
    /// p t1 .. tn
    App(Path<'ast>, &'ast [Sp<Type<'ast>>]),
}

#[derive(Clone, Copy, Debug)]
pub struct TypeDecl<'ast> {
    pub id: Id,
    pub vars: &'ast [Id],
    pub kind: TypeDeclKind<'ast>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub enum TypeDeclKind<'ast> {
    Alias(&'ast Sp<Type<'ast>>),
    Variant(&'ast [(Id, &'ast [Sp<Type<'ast>>])]),
}

#[derive(Clone, Copy, Debug)]
pub enum Item<'ast> {
    Type(&'ast [TypeDecl<'ast>]),
    Value(Id, Option<&'ast Sp<Type<'ast>>>, &'ast Expr<'ast>),
    External(Id, &'ast Sp<Type<'ast>>, Ident),
    Mod(Id, &'ast Sp<ModExpr<'ast>>),
}

#[derive(Clone, Copy, Debug)]
pub enum ModExpr<'ast> {
    Path(Path<'ast>),
    Struct(&'ast [Sp<Item<'ast>>]),
    Import(SourceId),
}

#[derive(Clone, Copy, Debug)]
pub struct Expr<'ast> {
    pub kind: ExprKind<'ast>,
    pub span: Span,
    pub ast_id: AstId,
}

impl<'ast> Expr<'ast> {
    pub fn new(kind: ExprKind<'ast>, span: Span, ast_id: AstId) -> Self {
        Self { kind, span, ast_id }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ExprKind<'ast> {
    Path(Path<'ast>),
    Cons(Path<'ast>),
    Lit(Lit),
    Ann(&'ast Expr<'ast>, &'ast Sp<Type<'ast>>),
    Tuple(&'ast [Expr<'ast>]),
    Vector(&'ast [Expr<'ast>]),
    Case(&'ast Expr<'ast>, &'ast [(Pat<'ast>, Expr<'ast>)]),
    If(&'ast Expr<'ast>, &'ast Expr<'ast>, &'ast Expr<'ast>),
    Lambda(Lambda<'ast>),
    Call(&'ast Expr<'ast>, &'ast [Expr<'ast>]),
    Let(&'ast [(Pat<'ast>, Expr<'ast>)], &'ast Expr<'ast>),
    Seq(&'ast Expr<'ast>, &'ast Expr<'ast>),
}

#[derive(Clone, Copy, Debug)]
pub struct Lambda<'ast> {
    pub args: &'ast [Pat<'ast>],
    pub body: &'ast Expr<'ast>,
}

#[derive(Clone, Copy, Debug)]
pub struct Pat<'ast> {
    pub kind: PatKind<'ast>,
    pub span: Span,
    pub ast_id: AstId,
}

impl<'ast> Pat<'ast> {
    pub fn new(kind: PatKind<'ast>, span: Span, ast_id: AstId) -> Self {
        Self { kind, span, ast_id }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum PatKind<'ast> {
    Wild,
    Lit(Lit),
    Var(Id),
    Ann(&'ast Pat<'ast>, &'ast Sp<Type<'ast>>),
    Tuple(&'ast [Pat<'ast>]),
    Cons(Path<'ast>, &'ast [Pat<'ast>]),
    Or(&'ast [Pat<'ast>]),
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Lit {
    Unit,
    Bool(bool),
    Int32(Sym),
    Str(Sym),
}

impl Lit {
    pub fn base_type(&self) -> BaseType {
        match self {
            Lit::Unit => BaseType::Unit,
            Lit::Bool(_) => BaseType::Bool,
            Lit::Int32(_) => BaseType::Int32,
            Lit::Str(_) => BaseType::Str,
        }
    }
}

pub trait AstVisitor<'ast>: Sized {
    fn visit_program(&mut self, program: &'ast Program<'ast>) {
        for unit in program.imports.values() {
            self.visit_comp_unit(unit);
        }
        self.visit_comp_unit(program.unit);
        self.visit_expr(program.main);
    }

    fn visit_comp_unit(&mut self, unit: &'ast CompUnit<'ast>) {
        for item in unit.items {
            self.visit_item(item);
        }
    }

    fn visit_item(&mut self, item: &'ast Item<'ast>) {
        match item {
            Item::Type(..) => (),
            Item::External(..) => (),
            Item::Value(_, _, expr) => self.visit_expr(expr),
            Item::Mod(_, mod_expr) => self.visit_mod_expr(mod_expr),
        }
    }

    fn visit_mod_expr(&mut self, mod_expr: &'ast ModExpr<'ast>) {
        match mod_expr {
            ModExpr::Struct(items) => {
                for item in items.iter() {
                    self.visit_item(item);
                }
            }
            ModExpr::Path(_) => (),
            ModExpr::Import(_) => (),
        }
    }

    fn visit_expr(&mut self, expr: &'ast Expr<'ast>) {
        expr.visit_with(self);
    }

    fn visit_pat(&mut self, pat: &'ast Pat<'ast>) {
        pat.visit_with(self);
    }
}

impl<'ast> Expr<'ast> {
    pub fn visit_with<V>(&self, v: &mut V)
    where
        V: AstVisitor<'ast>,
    {
        match self.kind {
            ExprKind::Path(_) | ExprKind::Cons(_) | ExprKind::Lit(_) => (),
            ExprKind::Ann(expr, _) => v.visit_expr(expr),
            ExprKind::Tuple(exprs) | ExprKind::Vector(exprs) => {
                exprs.iter().for_each(|expr| v.visit_expr(expr))
            }
            ExprKind::Case(expr, arms) => {
                v.visit_expr(expr);
                arms.iter().for_each(|(pat, expr)| {
                    v.visit_pat(pat);
                    v.visit_expr(expr);
                });
            }
            ExprKind::If(cond, then, els) => {
                v.visit_expr(cond);
                v.visit_expr(then);
                v.visit_expr(els);
            }
            ExprKind::Lambda(lambda) => {
                lambda.args.iter().for_each(|arg| v.visit_pat(arg));
                v.visit_expr(lambda.body);
            }
            ExprKind::Call(expr, args) => {
                v.visit_expr(expr);
                args.iter().for_each(|arg| v.visit_expr(arg));
            }
            ExprKind::Let(binds, expr) => {
                binds.iter().for_each(|(pat, expr)| {
                    v.visit_pat(pat);
                    v.visit_expr(expr);
                });
                v.visit_expr(expr);
            }
            ExprKind::Seq(expr1, expr2) => {
                v.visit_expr(expr1);
                v.visit_expr(expr2);
            }
        }
    }
}

impl<'ast> Pat<'ast> {
    pub fn visit_with<V>(&self, v: &mut V)
    where
        V: AstVisitor<'ast>,
    {
        match self.kind {
            PatKind::Wild | PatKind::Lit(_) | PatKind::Var(_) => (),
            PatKind::Ann(pat, _) => v.visit_pat(pat),
            PatKind::Cons(_, pats) | PatKind::Tuple(pats) | PatKind::Or(pats) => {
                pats.iter().for_each(|pat| v.visit_pat(pat))
            }
        }
    }
}
