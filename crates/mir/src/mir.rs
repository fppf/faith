use std::rc::Rc;

use base::{hash::Map, index::IndexVec};
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

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct JoinId(pub u32);

#[derive(Clone, Copy, Debug)]
pub enum Value {
    Var(Var),
    Lit(Lit),
    External(Sym),
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

#[derive(Clone, Debug)]
pub struct Call {
    pub func: Var,
    pub args: Vec<Value>,
}

#[derive(Clone, Debug)]
pub struct Join {
    pub id: JoinId,
    pub args: Vec<Var>,
    pub body: Box<Expr>,
}

#[derive(Clone, Debug)]
pub enum Pat {
    Wild,
    Lit(Lit),
    Cons(Var, Vec<Pat>),
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: Var,
    pub args: Vec<Var>,
    pub body: Box<Expr>,
    pub recursive: bool,
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
