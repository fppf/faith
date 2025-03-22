use std::{
    fmt,
    ops::{Deref, DerefMut},
};

use crate::{
    Lit, MAIN_LABEL, Value,
    mir::{Expr, Label, Module},
};

use base::pp::{Doc, DocArena, DocBuilder, INDENT, PRETTY_WIDTH, Superscript, ToDoc};

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "l{}", Superscript(self.as_u32()))
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Unit => "()".fmt(f),
            Lit::Bool(b) => b.fmt(f),
            Lit::Int32(n) => n.fmt(f),
            Lit::Str(s) => write!(f, "\"{s}\""),
        }
    }
}

impl<'a> ToDoc<'a> for Label {
    fn to_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        arena.text(self.to_string())
    }
}

impl<'a> ToDoc<'a> for Lit {
    fn to_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        arena.text(self.to_string())
    }
}

impl Value {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match self {
            Value::Label(l) => l.to_doc(arena),
            Value::Lit(l) => l.to_doc(arena),
            Value::External(s) => arena
                .text("external")
                .append(
                    arena
                        .text(s.as_str().to_string())
                        .enclose(arena.text("("), arena.text(")")),
                )
                .group(),
        }
    }
}

impl Expr {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        // FIXME
        match self {
            Expr::Value(v) => v.to_doc(arena),
            Expr::Tuple(vs) => arena
                .intersperse(vs.iter().map(|v| v.to_doc(arena)), arena.brk(", "))
                .enclose("(", ")")
                .group(),
            Expr::Vector(vs) => {
                todo!()
            }
            Expr::Let(l, e1, e2) => arena
                .text("let ")
                .append(*l)
                .append(" = ")
                .append(e1.to_doc(arena))
                .append(" in")
                .append(arena.space())
                .append(e2.to_doc(arena).nest(INDENT)),
            Expr::Proj(l, i) => l.to_doc(arena).append(".").append(i.to_string()),
            Expr::Lambda(args, body) => body.to_doc(arena),
            Expr::Call(f, args) => f.to_doc(arena),
            Expr::Case(l, _tree) => l.to_doc(arena),
            Expr::If(l, e1, e2) => l.to_doc(arena),
        }
    }
}

impl Module {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        let mut doc = arena.empty();
        for item in &self.items {
            doc = doc
                .append("val ")
                .append(item.label)
                .append(" =")
                .append(arena.space())
                .append(item.body.to_doc(arena).nest(INDENT))
                .append(arena.line());
        }
        doc
    }
}
