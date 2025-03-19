use base::{hash::Map, index::IndexVec};
use span::Sym;

use crate::match_compile::DecisionTree;

base::newtype_index! {
    pub struct MirId {}
}

base::newtype_index! {
    pub struct Label {}
}

pub const MAIN_LABEL: Label = Label::ZERO;

#[derive(Default, Debug)]
pub struct Module {
    pub items: IndexVec<MirId, Item>,
    pub label_to_mir_id: Map<Label, MirId>,
}

#[derive(Debug)]
pub struct Item {
    pub label: Label,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Proj(Box<Expr>, usize),
    Unwrap(Box<Expr>),
    External(Sym),
    Value(Value),
    Lambda(Vec<Label>, Box<Expr>),
    Call(Label, Vec<Value>),
    Tuple(Vec<Expr>),
    Vector(Vec<Expr>),
    Let(Label, Box<Expr>, Box<Expr>),
    Case(Label, DecisionTree),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Dup(Box<Expr>),
    Drop(Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum Value {
    Lit(Lit),
    Label(Label),
}

#[derive(Clone, Debug)]
pub enum Lit {
    Unit,
    Bool(bool),
    Int32(i32),
    Str(Sym),
}
