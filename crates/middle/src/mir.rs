use std::{cell::Cell, rc::Rc};

use base::hash::{IndexSet, Set};
use slotmap::{KeyData, SlotMap, new_key_type};
use span::Sym;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Var {
    pub sym: Sym,
    pub stamp: u32,
}

impl Var {
    fn new(sym: Sym, stamp: u32) -> Self {
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

new_key_type! { pub struct FuncId; }
new_key_type! { pub struct JoinId; }
new_key_type! { pub struct ExprId; }
new_key_type! { pub struct CallId; }

#[derive(Default, Debug)]
pub struct MirCtxt {
    pub funcs: SlotMap<FuncId, Func>,
    pub joins: SlotMap<JoinId, Join>,
    pub exprs: SlotMap<ExprId, Expr>,
    pub calls: SlotMap<CallId, Call>,
    var_counter: Cell<u32>,
}

impl MirCtxt {
    pub fn new_func(&mut self, func: Func) -> FuncId {
        self.funcs.insert(func)
    }

    pub fn new_join(&mut self, args: Vec<Var>, body: ExprId) -> JoinId {
        self.joins.insert_with_key(|id| Join { id, args, body })
    }

    pub fn new_expr(&mut self, kind: ExprKind) -> ExprId {
        self.exprs.insert(Expr::new(kind))
    }

    pub fn new_call(&mut self, call: Call) -> CallId {
        self.calls.insert(call)
    }

    pub fn new_var(&self, sym: Sym) -> Var {
        let stamp = self.var_counter.get();
        self.var_counter.update(|c| c + 1);
        Var::new(sym, stamp)
    }
}

#[derive(Debug)]
pub struct Program {
    pub ctxt: MirCtxt,
    pub joins: IndexSet<JoinId>,
    pub funcs: IndexSet<FuncId>,
    pub main: ExprId,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    //pub ty: Ty,
}

impl Expr {
    pub(crate) const SENTINEL: Self = Expr::new(ExprKind::Return(Value::Lit(Lit::Unit)));

    pub const fn new(kind: ExprKind) -> Self {
        Self { kind }
    }
}

pub fn free_vars(ctxt: &MirCtxt, expr_id: ExprId) -> IndexSet<Var> {
    let mut fv = FreeVars::default();
    fv.expr_vars(ctxt, expr_id);
    fv.vars
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    // let lhs = rhs in body
    Let { lhs: Var, rhs: Rhs, body: ExprId },
    // let func in body
    LetFunc { func_id: FuncId, body: ExprId },
    // let join in body
    LetJoin { join_id: JoinId, body: ExprId },
    // tail call
    Tail(CallId),
    // external tail calls
    ExternalCall(Var, Vec<Var>),
    // jump(id, v1, ..., vn)
    Jump(JoinId, Vec<Value>),
    // return(v)
    Return(Value),
    // case v of { p1 => e1, ..., pn => en }
    Case(Value, Vec<(Pat, ExprId)>),
}

#[derive(Default)]
pub struct FreeVars {
    pub bound: Set<Var>,
    pub vars: IndexSet<Var>,
}

impl FreeVars {
    pub fn func_vars(&mut self, ctxt: &MirCtxt, func_id: FuncId) {
        let func = &ctxt.funcs[func_id];

        self.bind_var(func.name);

        for var in &func.args {
            self.bind_var(*var);
        }
        self.expr_vars(ctxt, func.body);
    }

    pub fn join_vars(&mut self, ctxt: &MirCtxt, join_id: JoinId) {
        let join = &ctxt.joins[join_id];

        for var in &join.args {
            self.bind_var(*var);
        }
        self.expr_vars(ctxt, join.body);
    }

    pub fn expr_vars(&mut self, ctxt: &MirCtxt, expr: ExprId) {
        let expr = &ctxt.exprs[expr];
        match &expr.kind {
            ExprKind::Let { lhs, rhs, body } => {
                self.bind_var(*lhs);
                self.rhs_vars(ctxt, rhs);
                self.expr_vars(ctxt, *body);
            }
            ExprKind::LetFunc {
                func_id: func,
                body,
            } => {
                self.func_vars(ctxt, *func);
                self.expr_vars(ctxt, *body);
            }
            ExprKind::LetJoin { join_id, body } => {
                self.join_vars(ctxt, *join_id);
                self.expr_vars(ctxt, *body);
            }
            ExprKind::Tail(call) => self.call_vars(ctxt, *call),
            ExprKind::ExternalCall(_, args) => {
                for var in args {
                    self.add_var(*var);
                }
            }
            ExprKind::Jump(_, vals) => {
                for val in vals {
                    self.value_vars(val);
                }
            }
            ExprKind::Return(val) => self.value_vars(val),
            ExprKind::Case(val, items) => {
                self.value_vars(val);
                for (_pat, expr) in items {
                    self.expr_vars(ctxt, *expr);
                }
            }
        }
    }

    fn call_vars(&mut self, ctxt: &MirCtxt, call_id: CallId) {
        let call = &ctxt.calls[call_id];
        self.add_var(call.func_var);
        for val in &call.args {
            self.value_vars(val);
        }
    }

    fn value_vars(&mut self, value: &Value) {
        match value {
            Value::Var(var) => self.add_var(*var),
            Value::Lit(_) => (),
            Value::Ptr(_) => (),
        }
    }

    fn rhs_vars(&mut self, ctxt: &MirCtxt, rhs: &Rhs) {
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
            Rhs::Call(call) => self.call_vars(ctxt, *call),
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
}

#[derive(Clone, Copy, Debug)]
pub enum Value {
    Var(Var),
    Lit(Lit),
    Ptr(Var),
}

#[derive(Clone, Debug)]
pub enum Rhs {
    Value(Value),
    Proj(Var, usize),
    Cons(Var, Vec<Value>),
    Tuple(Vec<Value>),
    Vector(Vec<Value>),
    Call(CallId),
}

#[derive(Clone, Debug)]
pub struct Call {
    pub func_var: Var,
    pub args: Vec<Value>,
}

#[derive(Clone, Debug)]
pub struct Join {
    pub id: JoinId,
    pub args: Vec<Var>,
    pub body: ExprId,
}

#[derive(Clone, Copy, Debug)]
pub enum Pat {
    Lit(Lit),
    Tuple(usize),
    Cons(Var),
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: Var,
    pub args: Vec<Var>,
    pub body: ExprId,
    pub recursive: bool,
}

impl Func {
    pub(crate) fn sentinel() -> Self {
        Self {
            name: Var::new(Sym::intern("~"), 0),
            args: Vec::new(),
            body: ExprId(KeyData::default()),
            recursive: false,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lit {
    Unit,
    EmptyVector,
    Bool(bool),
    Int32(i32),
    Str(Sym),
}
