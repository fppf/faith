use std::fmt;

use base::hash::Map;
use span::{Ident, SourceId, Sp, Span, Sym};
use syntax::ast::Lit;

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

impl<'t> fmt::Display for Var<'t> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}~{}", self.id, self.res)?;
        if let Some(ty) = self.typ {
            write!(f, ": {ty}")?;
        }
        Ok(())
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
    pub fn new(kind: ExprKind<'t>, span: Span) -> Self {
        Self {
            kind,
            span,
            typ: None,
        }
    }

    pub fn visit_with<V>(&mut self, v: &mut V)
    where
        V: HirVisitor<'t>,
    {
        match &mut self.kind {
            ExprKind::Var(var) => v.visit_var(var),
            ExprKind::Lit(_) => (),
            ExprKind::Ann(expr, _) => v.visit_expr(expr),
            ExprKind::Tuple(exprs) => exprs.iter_mut().for_each(|expr| v.visit_expr(expr)),
            ExprKind::Vector(exprs) => exprs.iter_mut().for_each(|expr| v.visit_expr(expr)),
            ExprKind::Case(expr, arms) => {
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
            ExprKind::Let(binds, expr) => {
                binds.iter_mut().for_each(|(pat, expr)| {
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

#[derive(Clone, Debug)]
pub enum ExprKind<'t> {
    Var(Var<'t>),
    Lit(Lit),
    Ann(Box<Expr<'t>>, Sp<Ty<'t>>),
    Tuple(Vec<Expr<'t>>),
    Vector(Vec<Expr<'t>>),
    Case(Box<Expr<'t>>, Vec<(Pat<'t>, Expr<'t>)>),
    If(Box<Expr<'t>>, Box<Expr<'t>>, Box<Expr<'t>>),
    Lambda(Lambda<'t>),
    Call(Box<Expr<'t>>, Vec<Expr<'t>>),
    Let(Vec<(Pat<'t>, Expr<'t>)>, Box<Expr<'t>>),
    Seq(Box<Expr<'t>>, Box<Expr<'t>>),
}

#[derive(Clone, Debug)]
pub struct Lambda<'t> {
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
    pub fn new(kind: PatKind<'t>, span: Span) -> Self {
        Self {
            kind,
            span,
            typ: None,
        }
    }

    pub fn visit_with<V>(&mut self, v: &mut V)
    where
        V: HirVisitor<'t>,
    {
        match &mut self.kind {
            PatKind::Wild => (),
            PatKind::Lit(_) => (),
            PatKind::Var(var) => v.visit_var(var),
            PatKind::Ann(pat, _) => v.visit_pat(pat),
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
    Ann(Box<Pat<'t>>, Sp<Ty<'t>>),
    Tuple(Vec<Pat<'t>>),
    Cons(Var<'t>, Vec<Pat<'t>>),
    Or(Vec<Pat<'t>>),
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
