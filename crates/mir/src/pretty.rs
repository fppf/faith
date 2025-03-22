use std::{
    fmt,
    ops::{Deref, DerefMut},
};

use crate::{
    Lit, MAIN_LABEL, Value,
    mir::{Expr, Label, Module},
};

use base::pp::{Doc, DocArena, DocBuilder, INDENT, IntoDoc, PRETTY_WIDTH, Superscript};

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

impl<'a> IntoDoc<'a> for Label {
    fn into_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        arena.text(self.to_string())
    }
}

impl<'a> IntoDoc<'a> for Lit {
    fn into_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        arena.text(self.to_string())
    }
}

impl Value {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match self {
            Value::Label(l) => l.into_doc(arena),
            Value::Lit(l) => l.into_doc(arena),
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
        match self {
            Expr::Value(v) => v.to_doc(arena),
            Expr::Tuple(vs) => arena
                .intersperse(vs.iter().map(|v| v.to_doc(arena)), arena.brk(", "))
                .enclose("(", ")")
                .group(),
            Expr::Vector(vs) => arena
                .intersperse(vs.iter().map(|v| v.to_doc(arena)), arena.brk(", "))
                .enclose("[", "]")
                .group(),
            Expr::Let(l, e1, e2) => {
                let bind_doc = arena
                    .text("let")
                    .space(*l)
                    .space("=")
                    .space(e1.to_doc(arena));
                let body_doc = e2.to_doc(arena);
                bind_doc.space("in").group().space(body_doc)
            }
            Expr::Proj(l, i) => l.into_doc(arena).append(".").append(i.to_string()).group(),
            Expr::Lambda(args, body) => body.to_doc(arena),
            Expr::Call(f, args) => f
                .into_doc(arena)
                .space(arena.intersperse(args.iter().map(|arg| arg.to_doc(arena)), arena.space()))
                .enclose("(", ")")
                .group(),
            Expr::Case(l, _tree) => {
                let arms = arena.text("TODO");
                arena
                    .text("case")
                    .space(*l)
                    .space(arms.enclose("{", "}"))
                    .group()
            }
            Expr::If(l, e1, e2) => {
                let cond_doc = arena.text("if").space(*l).nest(INDENT).group();
                let then_doc = arena
                    .text("then")
                    .space(e1.to_doc(arena))
                    .nest(INDENT)
                    .group();
                let else_doc = arena
                    .text("else")
                    .space(e2.to_doc(arena))
                    .nest(INDENT)
                    .group();
                cond_doc.space(then_doc).space(else_doc).group()
            }
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
