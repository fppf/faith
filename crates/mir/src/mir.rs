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
    Value(Value),
    Let(Label, Box<Expr>, Box<Expr>),
    Call(Label, Vec<Value>),
    Lambda(Vec<Label>, Box<Expr>),
    Tuple(Vec<Value>),
    Vector(Vec<Value>),
    Proj(Label, usize),
    Case(Label, DecisionTree),
    If(Label, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Copy, Debug)]
pub enum Value {
    Lit(Lit),
    Label(Label),
    External(Sym),
}

#[derive(Clone, Copy, Debug)]
pub enum Lit {
    Unit,
    Bool(bool),
    Int32(i32),
    Str(Sym),
}
