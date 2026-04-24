use std::rc::Rc;

use base::{
    hash::{Map, Set},
    index::IndexVec,
};
use span::Sym;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Var {
    pub sym: Sym,
    pub stamp: u32,
}

impl Var {
    pub fn new(sym: Sym, stamp: u32) -> Self {
        Self { sym, stamp }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ty(Rc<TyKind>);

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TyKind {
    Var(Var),
    // n-ary function types
    // t1 t2 -> t3 is not the same as t1 -> t2 -> t3
    Arrow(Vec<Ty>, Ty),
}

#[derive(Debug)]
pub struct Program {
    pub funcs: Vec<Func>,
    pub main: Expr,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    //pub ty: Ty,
}

impl Expr {
    pub fn new(kind: ExprKind) -> Self {
        Self { kind }
    }

    pub fn free_vars(&self) -> Set<Var> {
        let mut fv = FreeVars::default();
        fv.expr_vars(&self);
        fv.vars
    }

    pub fn walk<V: MirVisitor>(&mut self, visit: &mut V) {
        match &mut self.kind {
            ExprKind::Let { lhs, rhs, body } => {
                visit.visit_var(lhs);
                visit.visit_rhs(rhs);
                visit.visit_expr(body);
            }
            ExprKind::LetFunc { func, body } => {
                visit.visit_func(func);
                visit.visit_expr(body);
            }
            ExprKind::LetJoin { join, body } => {
                visit.visit_expr(body);
            }
            ExprKind::Tail(call) => visit.visit_call(call),
            ExprKind::Jump(_join_id, vals) => {
                for val in vals {
                    visit.visit_value(val);
                }
            }
            ExprKind::Return(val) => visit.visit_value(val),
            ExprKind::Case(val, arms) => {
                visit.visit_value(val);
                for (pat, expr) in arms {
                    visit.visit_pat(pat);
                    visit.visit_expr(expr);
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    // let lhs = rhs in body
    Let { lhs: Var, rhs: Rhs, body: Box<Expr> },
    // let func in body
    LetFunc { func: Func, body: Box<Expr> },
    // let join in body
    LetJoin { join: Join, body: Box<Expr> },
    // tail call
    Tail(Call),
    // jump(id, v1, ..., vn)
    Jump(JoinId, Vec<Value>),
    // return(v)
    Return(Value),
    // case v of { p1 => e1, ..., pn => en }
    Case(Value, Vec<(Pat, Expr)>),
}

#[derive(Default)]
pub struct FreeVars {
    pub bound: Set<Var>,
    pub vars: Set<Var>,
}

impl FreeVars {
    pub fn func_vars(&mut self, func: &Func) {
        self.bind_var(func.name);

        for var in &func.args {
            self.bind_var(*var);
        }
        self.expr_vars(&func.body);

        // Argument variables are only in scope for function body
        for var in &func.args {
            self.unbind_var(*var);
        }
    }

    pub fn join_vars(&mut self, join: &Join) {
        for var in &join.args {
            self.bind_var(*var);
        }
        self.expr_vars(&join.body);

        // Argument variables are only in scope for join body
        for var in &join.args {
            self.unbind_var(*var);
        }
    }

    pub fn expr_vars(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Let { lhs, rhs, body } => {
                self.bind_var(*lhs);
                self.rhs_vars(rhs);
                self.expr_vars(body);
            }
            ExprKind::LetFunc { func, body } => {
                self.func_vars(func);
                self.expr_vars(body);
            }
            ExprKind::LetJoin { join, body } => {
                self.join_vars(join);
                self.expr_vars(body);
            }
            ExprKind::Tail(call) => self.call_vars(call),
            ExprKind::Jump(_, vals) => {
                for val in vals {
                    self.value_vars(val);
                }
            }
            ExprKind::Return(val) => self.value_vars(val),
            ExprKind::Case(val, items) => {
                self.value_vars(val);
                for (_pat, expr) in items {
                    self.expr_vars(expr);
                }
            }
        }
    }

    fn call_vars(&mut self, call: &Call) {
        self.add_var(call.func);
        for val in &call.args {
            self.value_vars(val);
        }
    }

    fn value_vars(&mut self, value: &Value) {
        match value {
            Value::Var(var) => self.add_var(*var),
            Value::Lit(_) => (),
        }
    }

    fn rhs_vars(&mut self, rhs: &Rhs) {
        match rhs {
            Rhs::Value(val) => self.value_vars(val),
            Rhs::Proj(v, _) => self.add_var(*v),
            Rhs::Cons(v, vals) => {
                self.add_var(*v);
                for val in vals {
                    self.value_vars(val);
                }
            }
            Rhs::Tuple(vals) | Rhs::Vector(vals) => {
                for val in vals {
                    self.value_vars(val);
                }
            }
            Rhs::Call(call) => self.call_vars(call),
        }
    }

    fn add_var(&mut self, var: Var) {
        if !self.bound.contains(&var) {
            self.vars.insert(var);
        }
    }

    fn bind_var(&mut self, var: Var) {
        self.bound.insert(var);
    }

    fn unbind_var(&mut self, var: Var) {
        self.bound.remove(&var);
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct JoinId(pub u32);

#[derive(Clone, Copy, Debug)]
pub enum Value {
    Var(Var),
    Lit(Lit),
}

impl Value {
    pub fn walk<V: MirVisitor>(&mut self, visit: &mut V) {
        match self {
            Value::Var(var) => visit.visit_var(var),
            Value::Lit(_) => (),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Rhs {
    Value(Value),
    Proj(Var, usize),
    Cons(Var, Vec<Value>),
    Tuple(Vec<Value>),
    Vector(Vec<Value>),
    Call(Call),
}

impl Rhs {
    pub fn walk<V: MirVisitor>(&mut self, visit: &mut V) {
        match self {
            Rhs::Value(val) => visit.visit_value(val),
            Rhs::Proj(var, _) => visit.visit_var(var),
            Rhs::Cons(var, vals) => {
                visit.visit_var(var);
                for val in vals {
                    visit.visit_value(val);
                }
            }
            Rhs::Tuple(vals) | Rhs::Vector(vals) => {
                for val in vals {
                    visit.visit_value(val);
                }
            }
            Rhs::Call(call) => visit.visit_call(call),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Call {
    pub func: Var,
    pub args: Vec<Value>,
}

impl Call {
    pub fn walk<V: MirVisitor>(&mut self, visit: &mut V) {
        visit.visit_var(&mut self.func);
        for val in &mut self.args {
            visit.visit_value(val);
        }
    }
}

#[derive(Clone, Debug)]
pub struct Join {
    pub id: JoinId,
    pub args: Vec<Var>,
    pub body: Box<Expr>,
}

impl Join {
    pub fn walk<V: MirVisitor>(&mut self, visit: &mut V) {
        for var in &mut self.args {
            visit.visit_var(var);
        }
        visit.visit_expr(&mut self.body);
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Pat {
    Lit(Lit),
    Tuple(usize),
    Cons(Var),
}

impl Pat {
    pub fn walk<V: MirVisitor>(&mut self, visit: &mut V) {
        match self {
            Pat::Lit(_) => (),
            Pat::Tuple(_) => (),
            Pat::Cons(var) => visit.visit_var(var),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: Var,
    pub args: Vec<Var>,
    pub body: Box<Expr>,
    pub recursive: bool,
}

impl Func {
    pub fn walk<V: MirVisitor>(&mut self, visit: &mut V) {
        visit.visit_var(&mut self.name);
        for var in &mut self.args {
            visit.visit_var(var);
        }
        visit.visit_expr(&mut self.body);
    }
}

#[derive(Clone, Debug)]
pub struct Closure {
    pub env: Map<Var, Value>,
    pub func: Func,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lit {
    Unit,
    EmptyVector,
    Bool(bool),
    Int32(i32),
    Str(Sym),
}

pub trait MirVisitor: Sized {
    fn visit_program(&mut self, program: &mut Program) {
        for func in &mut program.funcs {
            self.visit_func(func);
        }
        self.visit_expr(&mut program.main);
    }

    fn visit_func(&mut self, func: &mut Func) {
        func.walk(self);
    }

    fn visit_join(&mut self, join: &mut Join) {
        join.walk(self);
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        expr.walk(self);
    }

    fn visit_rhs(&mut self, rhs: &mut Rhs) {
        rhs.walk(self);
    }

    fn visit_call(&mut self, call: &mut Call) {
        call.walk(self);
    }

    fn visit_value(&mut self, value: &mut Value) {
        value.walk(self);
    }

    fn visit_pat(&mut self, pat: &mut Pat) {
        pat.walk(self);
    }

    fn visit_var(&mut self, _var: &mut Var) {}
}
