use std::{
    fmt,
    ops::{Deref, DerefMut},
};

use base::pp::{Doc, DocArena, DocBuilder, INDENT, IntoDoc, PRETTY_WIDTH, Subscript};

use crate::{Call, Expr, ExprKind, Func, Join, JoinId, Lit, Pat, Program, Rhs, Value, Var};

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.sym.as_str();
        write!(f, "{s}{}", Subscript(self.stamp))
    }
}

impl fmt::Display for JoinId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ".j{}", self.0)
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Unit => "()".fmt(f),
            Lit::EmptyVector => "[]".fmt(f),
            Lit::Bool(b) => b.fmt(f),
            Lit::Int32(n) => n.fmt(f),
            Lit::Str(s) => write!(f, "\"{s}\""),
        }
    }
}

impl<'a> IntoDoc<'a> for Var {
    fn into_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        self.to_string().into_doc(arena)
    }
}

impl<'a> IntoDoc<'a> for JoinId {
    fn into_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        self.to_string().into_doc(arena)
    }
}

impl<'a> IntoDoc<'a> for Lit {
    fn into_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        self.to_string().into_doc(arena)
    }
}

impl<'a> IntoDoc<'a> for Value {
    fn into_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match self {
            Value::Var(x) => x.into_doc(arena),
            Value::Lit(l) => l.into_doc(arena),
            Value::External(s) => arena
                .text("#")
                .append(arena.text(s.as_str().to_string()).enclose("(", ")"))
                .group(),
        }
    }
}

impl Expr {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match &self.kind {
            ExprKind::Let { lhs, rhs, body } => arena
                .text("let")
                .space(*lhs)
                .space("=")
                .space(rhs.to_doc(arena))
                .space("in")
                .append(arena.line())
                .append(body.to_doc(arena)),
            ExprKind::LetFunc { func, body } => arena
                .text("let ")
                .append(func.to_doc(arena).nest(2))
                .append(arena.line())
                .append("in")
                .append(arena.line())
                .append(body.to_doc(arena)),
            ExprKind::LetJoin { join, body } => arena
                .text("let ")
                .append(join.to_doc(arena).nest(2))
                .append(arena.line())
                .append("in")
                .append(arena.line())
                .append(body.to_doc(arena)),
            ExprKind::Tail(call) => call.to_doc(arena),
            ExprKind::Jump(join_id, vs) => join_id
                .into_doc(arena)
                .space(arena.intersperse(vs.iter().copied(), arena.space()))
                .group(),
            ExprKind::Return(v) => arena.text("ret").space(*v),
            ExprKind::Case(v, arms) => {
                let arms = arena.line().append(arena.intersperse(
                    arms.iter().map(|(p, e)| {
                        p.to_doc(arena)
                            .space("=> ")
                            .group()
                            .append(e.to_doc(arena))
                            .nest(2)
                    }),
                    arena.text(",").append(arena.line()),
                ));
                arena
                    .text("case")
                    .space(*v)
                    .space("{")
                    .append(arms.nest(2))
                    .append(",")
                    .append(arena.line())
                    .append("}")
            }
        }
    }
}

impl Rhs {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match self {
            Rhs::Value(v) => v.into_doc(arena),
            Rhs::Proj(x, i) => x.into_doc(arena).append(".").append(i.to_string()).group(),
            Rhs::Cons(var, vs) => todo!(),
            Rhs::Tuple(vs) => arena
                .intersperse(vs.iter().map(|v| v.into_doc(arena)), arena.text(", "))
                .enclose("(", ")")
                .group(),
            Rhs::Vector(vs) => arena
                .intersperse(vs.iter().map(|v| v.into_doc(arena)), arena.text(", "))
                .enclose("[", "]")
                .group(),
            Rhs::Call(call) => call.to_doc(arena),
        }
    }
}

impl Pat {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match self {
            Pat::Wild => arena.text("_"),
            Pat::Lit(lit) => lit.into_doc(arena),
            Pat::Cons(c, _ps) => c.into_doc(arena),
        }
    }
}

impl Func {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        arena
            .text("fn")
            .space(self.name)
            .space(arena.intersperse(self.args.iter().copied(), arena.space()))
            .space("=")
            .group()
            .append(arena.line())
            .append(self.body.to_doc(arena))
    }
}

impl Join {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        arena
            .text("join")
            .space(self.id)
            .space(arena.intersperse(self.args.iter().copied(), arena.space()))
            .space("=")
            .group()
            .append(arena.line())
            .append(self.body.to_doc(arena))
    }
}

impl Call {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        self.func
            .into_doc(arena)
            .space(arena.intersperse(
                self.args.iter().map(|arg| arg.into_doc(arena)),
                arena.space(),
            ))
            .group()
    }
}

impl Program {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        let mut doc = arena.empty();
        for func in &self.funcs {
            doc = doc
                .append(func.to_doc(arena).nest(2))
                .append(arena.line())
                .append(arena.line());
        }
        doc.append(self.main.to_doc(arena))
    }
}
