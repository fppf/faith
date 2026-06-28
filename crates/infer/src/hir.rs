use std::{
    fmt,
    hash::{Hash, Hasher},
};

use base::{
    hash::Map,
    pp::{DocArena, DocBuilder, IntoDoc},
};
use span::{Ident, SourceId, Sp, Span, Sym};

pub use syntax::ast::Lit;

use crate::{Res, ty::Ty};

#[derive(Clone, Copy, Debug)]
pub struct Var<'t> {
    pub id: Ident,
    pub res: Res,
    pub span: Span,
    pub external: Option<Sym>,
    pub typ: Option<Ty<'t>>,
}

impl<'t> Var<'t> {
    pub fn new(id: Ident, res: Res, span: Span) -> Self {
        Self {
            id,
            res,
            span,
            external: None,
            typ: None,
        }
    }
}

impl<'t> PartialEq for Var<'t> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.res == other.res
    }
}

impl<'t> Eq for Var<'t> {}

impl<'t> Hash for Var<'t> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
        self.res.hash(state);
    }
}

impl<'t> fmt::Display for Var<'t> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.id, self.res)?;
        if let Some(ty) = self.typ {
            write!(f, ":{ty}")?;
        }
        Ok(())
    }
}

impl<'a, 't> IntoDoc<'a> for Var<'t> {
    fn into_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        self.to_string().into_doc(arena)
    }
}

/// The `main` expression is the entry point to the program.
#[derive(Clone, Debug)]
pub struct Program<'t> {
    pub imports: Map<SourceId, CompUnit<'t>>,
    pub unit: CompUnit<'t>,
    pub main: Expr<'t>,
}

/// A compilation unit, originating from a source file (`source_id`).
#[derive(Clone, Debug)]
pub struct CompUnit<'t> {
    pub source_id: SourceId,
    pub items: Vec<Item<'t>>,
}

#[derive(Clone, Debug)]
pub enum Item<'t> {
    Expr {
        var: Var<'t>,
        recursive: bool,
        expr: Expr<'t>,
        expected_typ: Option<Sp<Ty<'t>>>,
        typ: Option<Ty<'t>>,
    },
}

#[derive(Clone, Debug)]
pub struct Expr<'t> {
    pub kind: ExprKind<'t>,
    pub span: Span,
    pub typ: Option<Ty<'t>>,
}

impl<'t> Expr<'t> {
    pub fn new(kind: ExprKind<'t>, span: Span, typ: Option<Ty<'t>>) -> Self {
        Self { kind, span, typ }
    }

    pub fn visit_with<V>(&mut self, v: &mut V)
    where
        V: HirVisitor<'t>,
    {
        match &mut self.kind {
            ExprKind::Var(var) => v.visit_var(var),
            ExprKind::Lit(_) => (),
            ExprKind::Tuple(exprs) => exprs.iter_mut().for_each(|expr| v.visit_expr(expr)),
            ExprKind::Vector(exprs) => exprs.iter_mut().for_each(|expr| v.visit_expr(expr)),
            ExprKind::Case(expr, arms, _) => {
                v.visit_expr(expr);
                arms.iter_mut().for_each(|(pat, expr)| {
                    v.visit_pat(pat);
                    v.visit_expr(expr);
                });
            }
            ExprKind::If(cond_expr, then_expr, else_expr) => {
                v.visit_expr(cond_expr);
                v.visit_expr(then_expr);
                v.visit_expr(else_expr);
            }
            ExprKind::Lambda(lambda) => {
                lambda.args.iter_mut().for_each(|arg| v.visit_pat(arg));
                v.visit_expr(&mut lambda.body);
            }
            ExprKind::Call(head, args) => {
                v.visit_expr(head);
                args.iter_mut().for_each(|arg| v.visit_expr(arg));
            }
            ExprKind::ExternalCall(ext, args) => {
                v.visit_var(ext);
                args.iter_mut().for_each(|arg| v.visit_var(arg));
            }
            ExprKind::Cons(cons, args) => {
                v.visit_var(cons);
                args.iter_mut().for_each(|arg| v.visit_expr(arg));
            }
            ExprKind::Let(pat, expr, body) => {
                v.visit_pat(pat);
                v.visit_expr(expr);
                v.visit_expr(body);
            }
            ExprKind::Seq(expr1, expr2) => {
                v.visit_expr(expr1);
                v.visit_expr(expr2);
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind<'t> {
    Var(Var<'t>),
    Lit(Lit),
    Tuple(Vec<Expr<'t>>),
    Vector(Vec<Expr<'t>>),
    Case(
        Box<Expr<'t>>,
        Vec<(Pat<'t>, Expr<'t>)>,
        Option<CompiledCase<'t>>,
    ),
    If(Box<Expr<'t>>, Box<Expr<'t>>, Box<Expr<'t>>),
    Lambda(Lambda<'t>),
    Call(Box<Expr<'t>>, Vec<Expr<'t>>),
    ExternalCall(Var<'t>, Vec<Var<'t>>),
    Cons(Var<'t>, Vec<Expr<'t>>),
    Let(Pat<'t>, Box<Expr<'t>>, Box<Expr<'t>>),
    Seq(Box<Expr<'t>>, Box<Expr<'t>>),
}

#[derive(Clone, Debug)]
pub struct Lambda<'t> {
    pub name: Option<Ident>,
    pub args: Vec<Pat<'t>>,
    pub body: Box<Expr<'t>>,
}

#[derive(Clone, Debug)]
pub struct Pat<'t> {
    pub kind: PatKind<'t>,
    pub span: Span,
    pub typ: Option<Ty<'t>>,
}

impl<'t> Pat<'t> {
    pub fn new(kind: PatKind<'t>, span: Span, typ: Option<Ty<'t>>) -> Self {
        Self { kind, span, typ }
    }

    pub fn visit_with<V>(&mut self, v: &mut V)
    where
        V: HirVisitor<'t>,
    {
        match &mut self.kind {
            PatKind::Wild => (),
            PatKind::Lit(_) => (),
            PatKind::Var(var) => v.visit_var(var),
            PatKind::Tuple(pats) => pats.iter_mut().for_each(|pat| v.visit_pat(pat)),
            PatKind::Cons(var, pats) => {
                v.visit_var(var);
                pats.iter_mut().for_each(|pat| v.visit_pat(pat));
            }
            PatKind::Or(pats) => pats.iter_mut().for_each(|pat| v.visit_pat(pat)),
        }
    }
}

#[derive(Clone, Debug)]
pub enum PatKind<'t> {
    Wild,
    Lit(Lit),
    Var(Var<'t>),
    Tuple(Vec<Pat<'t>>),
    Cons(Var<'t>, Vec<Pat<'t>>),
    Or(Vec<Pat<'t>>),
}

#[derive(Clone, Debug)]
pub struct CompiledCase<'t> {
    pub branch_var: Var<'t>,
    pub tree: DecisionTree<'t>,
}

#[derive(Clone, Debug)]
pub enum DecisionTree<'t> {
    Fail,
    Leaf(Body<'t>),
    Switch(Var<'t>, Vec<Case<'t>>),
}

#[derive(Clone, Debug)]
pub struct Case<'t> {
    pub constructor: Constructor<'t>,
    pub variables: Vec<Var<'t>>,
    pub tree: DecisionTree<'t>,
}

#[derive(Clone, Copy, Debug)]
pub enum Constructor<'t> {
    Unit,
    Bool(bool),
    Tuple(usize),
    Variant(Var<'t>, usize),
}

#[derive(Clone, Debug)]
pub struct Body<'t> {
    pub binds: Vec<(Var<'t>, Var<'t>)>,
    pub action: usize,
}

pub trait HirVisitor<'t>: Sized {
    fn visit_program(&mut self, program: &mut Program<'t>) {
        for unit in program.imports.values_mut() {
            self.visit_comp_unit(unit);
        }
        self.visit_comp_unit(&mut program.unit);
        self.visit_expr(&mut program.main);
    }

    fn visit_comp_unit(&mut self, unit: &mut CompUnit<'t>) {
        for item in &mut unit.items {
            self.visit_item(item);
        }
    }

    fn visit_item(&mut self, item: &mut Item<'t>) {
        match item {
            Item::Expr { expr, .. } => self.visit_expr(expr),
        }
    }

    fn visit_var(&mut self, _var: &mut Var<'t>) {}

    fn visit_expr(&mut self, expr: &mut Expr<'t>) {
        expr.visit_with(self);
    }

    fn visit_pat(&mut self, pat: &mut Pat<'t>) {
        pat.visit_with(self);
    }
}
