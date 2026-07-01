use std::fmt;

use base::pp::{DocArena, DocBuilder, IntoDoc, Subscript};

use crate::mir::{
    Call, CallKind, ExprId, ExprKind, FuncId, JoinId, Lit, MirCtxt, Pat, PrimType, Program, Rhs,
    Type, Value, Var,
};

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = self.sym.as_str();
        write!(f, "{s}{}", Subscript(self.stamp))
    }
}

impl fmt::Display for JoinId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ".j{}", self.index())
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
            Value::Ptr(f) => arena.text("*").append(f.into_doc(arena)),
        }
    }
}

impl ExprId {
    pub fn to_doc<'a>(self, ctxt: &MirCtxt, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        let expr = &ctxt.exprs[self];
        match &expr.kind {
            ExprKind::Let { lhs, rhs, body } => arena
                .text("let")
                .space(*lhs)
                .space("=")
                .space(rhs.to_doc(ctxt, arena))
                .space("in")
                .append(arena.line())
                .append(body.to_doc(ctxt, arena)),
            ExprKind::LetFunc {
                func_id: func,
                body,
            } => arena
                .text("let ")
                .append(func.to_doc(ctxt, arena).nest(2))
                .append(arena.line())
                .append("in")
                .append(arena.line())
                .append(body.to_doc(ctxt, arena)),
            ExprKind::LetJoin {
                join_id: join,
                body,
            } => arena
                .text("let ")
                .append(join.to_doc(ctxt, arena).nest(2))
                .append(arena.line())
                .append("in")
                .append(arena.line())
                .append(body.to_doc(ctxt, arena)),
            ExprKind::Call(call) => call.to_doc(ctxt, arena),
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
                            .append(arena.line())
                            .append(e.to_doc(ctxt, arena))
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
    pub fn to_doc<'a>(&self, ctxt: &MirCtxt, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match self {
            Rhs::Value(v) => v.into_doc(arena),
            Rhs::Proj(x, i) => x.into_doc(arena).append(".").append(i.to_string()).group(),
            Rhs::Cons(cons, vs) => cons
                .into_doc(arena)
                .append(
                    arena
                        .intersperse(vs.iter().map(|v| v.into_doc(arena)), arena.text(", "))
                        .enclose("(", ")"),
                )
                .group(),
            Rhs::Tuple(vs) => arena
                .intersperse(vs.iter().map(|v| v.into_doc(arena)), arena.text(", "))
                .enclose("(", ")")
                .group(),
            Rhs::Vector(vs) => arena
                .intersperse(vs.iter().map(|v| v.into_doc(arena)), arena.text(", "))
                .enclose("[", "]")
                .group(),
            Rhs::Call(call) => call.to_doc(ctxt, arena),
        }
    }
}

impl Pat {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match self {
            Pat::Lit(lit) => lit.into_doc(arena),
            Pat::Tuple(n) => arena.text(format!("(){n}")),
            Pat::Cons(c) => c.into_doc(arena),
        }
    }
}

impl fmt::Display for PrimType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimType::Unit => "()".fmt(f),
            PrimType::Bool => "bool".fmt(f),
            PrimType::Int32 => "i32".fmt(f),
            PrimType::Str => "str".fmt(f),
        }
    }
}

impl Type {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match self {
            Type::Prim(prim_type) => arena.text(prim_type.to_string()),
            Type::Generic(generic) => arena.text(generic.to_string()),
            Type::App(var, items) => todo!(),
            Type::Arrow(arg_typs, ret_typ) => arena
                .intersperse(
                    arg_typs.iter().map(|typ| typ.to_doc(arena)),
                    arena.text(", "),
                )
                .space("-> ")
                .append(ret_typ.to_doc(arena))
                .parens()
                .group(),
            Type::Tuple(typs) => arena
                .intersperse(typs.iter().map(|typ| typ.to_doc(arena)), arena.text(", "))
                .enclose("(", ")")
                .group(),
            Type::Vector(typ) => typ.to_doc(arena).brackets(),
        }
    }
}

impl FuncId {
    pub fn to_doc<'a>(self, ctxt: &MirCtxt, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        let func = &ctxt.funcs[self];
        arena
            .text("fn")
            .space(func.name)
            .space(arena.intersperse(func.args.iter().copied(), arena.space()))
            .space(": ")
            .append(func.typ.to_doc(arena))
            .group()
            .append(arena.line())
            .append(func.body.to_doc(ctxt, arena))
    }
}

impl JoinId {
    pub fn to_doc<'a>(self, ctxt: &MirCtxt, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        let join = &ctxt.joins[self];
        arena
            .text("join")
            .space(join.id)
            .space(arena.intersperse(join.args.iter().copied(), arena.space()))
            .space(":")
            .group()
            .append(arena.line())
            .append(join.body.to_doc(ctxt, arena))
    }
}

impl Call {
    pub fn to_doc<'a>(&self, _ctxt: &MirCtxt, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        let doc = self
            .func_var
            .into_doc(arena)
            .space(arena.intersperse(
                self.args.iter().map(|arg| arg.into_doc(arena)),
                arena.space(),
            ))
            .group();
        match self.kind {
            CallKind::Normal => doc,
            CallKind::External => doc.enclose("$(", ")"),
        }
    }
}

impl Program {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        let mut doc = arena.empty();

        for join in &self.joins {
            doc = doc
                .append(join.to_doc(&self.ctxt, arena).nest(2))
                .append(arena.line())
                .append(arena.line());
        }

        for func in &self.funcs {
            doc = doc
                .append(func.to_doc(&self.ctxt, arena).nest(2))
                .append(arena.line())
                .append(arena.line());
        }
        doc.append(self.main.to_doc(&self.ctxt, arena))
    }
}
