use std::fmt;

use base::pp::{DocArena, DocBuilder, PRETTY_WIDTH};

use crate::ast::*;

impl fmt::Display for Program<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let arena = DocArena::default();
        let doc = self.main.to_doc(&arena, Parens::Top);

        doc.pretty_string(PRETTY_WIDTH).fmt(f)
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.ident.fmt(f)
    }
}

impl fmt::Display for Path<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.root.fmt(f)?;
        for id in self.access {
            write!(f, ".{id}")?;
        }
        Ok(())
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => "()".fmt(f),
            Self::Bool(b) => b.fmt(f),
            Self::Int32(n) => write!(f, "{n}i32"),
            Self::Str(s) => write!(f, "\"{}\"", s.as_str()),
        }
    }
}

impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseType::Unit => "()",
            BaseType::Bool => "bool",
            BaseType::Str => "str",
            BaseType::Int32 => "i32",
        }
        .fmt(f)
    }
}

#[derive(Clone, Copy, PartialEq, PartialOrd)]
enum Parens {
    // Appears in a position that does not require parentheses.
    Top,

    // Appears in a position that might require parentheses.
    Inner,
}

impl Type<'_> {
    // If this type, as occuring inside another type,
    // might need to be wrapped in parentheses.
    fn needs_inner_parens(&self) -> bool {
        match *self {
            Type::Base(_) | Type::Var(_) | Type::Tuple(_) | Type::Vector(_) | Type::Row(..) => {
                false
            }
            Type::App(_, args) => !args.is_empty(),
            Type::Arrow(..) => true,
        }
    }

    fn to_doc<'a>(&self, arena: &'a DocArena<'a>, parens: Parens) -> DocBuilder<'a> {
        let doc = match self {
            Type::Base(base) => arena.text(base.to_string()),
            Type::Var(id) => arena.text(id.to_string()),
            Type::Arrow(from, to) => from
                .to_doc(arena, Parens::Inner)
                .append(" -> ")
                .append(to.to_doc(arena, Parens::Inner))
                .group(),
            Type::Tuple(typs) => arena
                .intersperse(typs.iter().map(|typ| typ.to_doc(arena, Parens::Top)), ", ")
                .group()
                .parens(),
            Type::Vector(typ) => typ.to_doc(arena, Parens::Top).brackets(),
            Type::App(path, args) => {
                if args.is_empty() {
                    arena.text(path.to_string())
                } else {
                    arena
                        .text(path.to_string())
                        .space(arena.intersperse(
                            args.iter().map(|arg| arg.to_doc(arena, Parens::Inner)),
                            " ",
                        ))
                        .group()
                }
            }
            Type::Row(..) => unreachable!("row types unsupported"),
        };

        if self.needs_inner_parens() && parens >= Parens::Inner {
            doc.parens()
        } else {
            doc
        }
    }
}

impl Pat<'_> {
    // If this pattern, as occuring inside another pattern,
    // might need to be wrapped in parentheses.
    fn needs_inner_parens(&self) -> bool {
        match self.kind {
            PatKind::Wild
            | PatKind::Lit(_)
            | PatKind::Var(_)
            | PatKind::Ann(..)
            | PatKind::Tuple(_) => false,
            PatKind::Cons(_, args) => !args.is_empty(),
            PatKind::Or(_) => true,
        }
    }

    fn to_doc<'a>(&self, arena: &'a DocArena<'a>, parens: Parens) -> DocBuilder<'a> {
        let doc = match self.kind {
            PatKind::Wild => arena.text("_"),
            PatKind::Lit(lit) => arena.text(lit.to_string()),
            PatKind::Var(id) => arena.text(id.to_string()),
            PatKind::Ann(pat, typ) => pat
                .to_doc(arena, Parens::Top)
                .append(" : ")
                .append(typ.to_doc(arena, Parens::Top))
                .group()
                .parens(),
            PatKind::Tuple(pats) => arena
                .intersperse(pats.iter().map(|pat| pat.to_doc(arena, Parens::Top)), ", ")
                .group()
                .parens(),
            PatKind::Cons(path, args) => {
                if args.is_empty() {
                    arena.text(path.to_string())
                } else {
                    arena
                        .text(path.to_string())
                        .space(arena.intersperse(
                            args.iter().map(|arg| arg.to_doc(arena, Parens::Inner)),
                            " ",
                        ))
                        .group()
                }
            }
            PatKind::Or(pats) => {
                arena.intersperse(pats.iter().map(|pat| pat.to_doc(arena, Parens::Top)), " | ")
            }
        };

        if self.needs_inner_parens() && parens >= Parens::Inner {
            doc.parens()
        } else {
            doc
        }
    }
}

impl Expr<'_> {
    // If this expression, as occuring inside another expression,
    // might need to be wrapped in parentheses.
    fn needs_inner_parens(&self) -> bool {
        match self.kind {
            ExprKind::Path(_)
            | ExprKind::Lit(_)
            | ExprKind::Ann(..)
            | ExprKind::Tuple(_)
            | ExprKind::Vector(_) => false,
            ExprKind::Cons(_, args) => !args.is_empty(),
            ExprKind::Case(..)
            | ExprKind::If(..)
            | ExprKind::Lambda(_)
            | ExprKind::Call(..)
            | ExprKind::Let(..)
            | ExprKind::Seq(..) => true,
        }
    }

    fn to_doc<'a>(&self, arena: &'a DocArena<'a>, parens: Parens) -> DocBuilder<'a> {
        let doc = match self.kind {
            ExprKind::Path(path) => arena.text(path.to_string()),
            ExprKind::Lit(lit) => arena.text(lit.to_string()),
            ExprKind::Ann(expr, typ) => expr
                .to_doc(arena, Parens::Top)
                .append(" : ")
                .append(typ.to_doc(arena, Parens::Top))
                .group()
                .parens(),
            ExprKind::Tuple(exprs) => arena
                .intersperse(
                    exprs.iter().map(|expr| expr.to_doc(arena, Parens::Top)),
                    ", ",
                )
                .group()
                .parens(),
            ExprKind::Vector(exprs) => arena
                .intersperse(
                    exprs.iter().map(|expr| expr.to_doc(arena, Parens::Top)),
                    ", ",
                )
                .group()
                .brackets(),
            ExprKind::Call(expr, args) => expr.to_doc(arena, Parens::Inner).space(
                arena.intersperse(args.iter().map(|arg| arg.to_doc(arena, Parens::Inner)), " "),
            ),
            ExprKind::Lambda(lambda) => arena.text("\\").append(
                arena
                    .intersperse(
                        lambda
                            .args
                            .iter()
                            .map(|arg| arg.to_doc(arena, Parens::Inner)),
                        " ",
                    )
                    .append(" -> ")
                    .append(lambda.body.to_doc(arena, Parens::Top)),
            ),
            ExprKind::If(cond, expr1, expr2) => arena
                .text("if")
                .space(cond.to_doc(arena, Parens::Inner))
                .space("then")
                .space("")
                .append(expr1.to_doc(arena, Parens::Inner).nest(2))
                .space("else")
                .space("")
                .append(expr2.to_doc(arena, Parens::Inner).nest(2)),
            ExprKind::Case(expr, arms) => {
                let arms = arena.line().append(arena.intersperse(
                    arms.iter().map(|(p, e)| {
                        p.to_doc(arena, Parens::Top)
                            .space("=> ")
                            .group()
                            .append(arena.line())
                            .append(e.to_doc(arena, Parens::Top))
                            .nest(2)
                    }),
                    arena.text(",").append(arena.line()),
                ));
                arena
                    .text("case")
                    .space(expr.to_doc(arena, Parens::Inner))
                    .space("{")
                    .append(arms.nest(2))
                    .append(",")
                    .append(arena.line())
                    .append("}")
            }
            ExprKind::Cons(path, args) => {
                if args.is_empty() {
                    arena.text(path.to_string())
                } else {
                    arena
                        .text(path.to_string())
                        .space(arena.intersperse(
                            args.iter().map(|arg| arg.to_doc(arena, Parens::Inner)),
                            " ",
                        ))
                        .group()
                }
            }
            ExprKind::Let(binds, expr) => {
                let binds = if binds.len() == 1 {
                    let (p, e) = binds[0];
                    arena
                        .space()
                        .append(p.to_doc(arena, Parens::Top))
                        .append(" = ")
                        .append(e.to_doc(arena, Parens::Top))
                        .append(" ")
                } else {
                    arena
                        .line()
                        .append(arena.intersperse(
                            binds.iter().map(|(p, e)| {
                                p.to_doc(arena, Parens::Top)
                                    .append(" = ")
                                    .append(e.to_doc(arena, Parens::Top))
                                    .group()
                            }),
                            arena.text(",").append(arena.line()),
                        ))
                        .append(",")
                        .nest(2)
                        .append(arena.line())
                };
                arena
                    .text("let")
                    .append(binds)
                    .append("in")
                    .space(expr.to_doc(arena, Parens::Inner))
            }
            ExprKind::Seq(expr1, expr2) => expr1
                .to_doc(arena, Parens::Top)
                .append(";")
                .space(expr2.to_doc(arena, Parens::Top)),
        };

        if self.needs_inner_parens() && parens >= Parens::Inner {
            doc.parens()
        } else {
            doc
        }
    }
}
