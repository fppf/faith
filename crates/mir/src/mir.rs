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
    Label(Label),
    Proj(Box<Expr>, usize),
    Unwrap(Box<Expr>),
    External(Sym),
    Lit(hir::Lit),
    Lambda(Vec<Label>, Box<Expr>),
    App(Box<Expr>, Vec<Expr>),
    Tuple(Vec<Expr>),
    Vector(Box<Expr>),
    Let(Label, Box<Expr>, Box<Expr>),
    Case(Label, DecisionTree),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Dup(Box<Expr>),
    Drop(Box<Expr>),
}
