use std::{
    fmt,
    ops::{Deref, DerefMut},
};

use base::pp::*;

use crate::{
    CompUnit, Expr, ExprKind, HirId, Ident, Items, Lambda, Lit, NO_WEB, Pat, PatKind, Path,
    Program, Ty, TyKind, WebId,
};

impl fmt::Display for WebId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Superscript(self.as_u32()).fmt(f)
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Unit => "()".fmt(f),
            Lit::Bool(b) => b.fmt(f),
            Lit::Str(s) => write!(f, "\"{s}\""),
            Lit::Int32(n) => n.fmt(f),
        }
    }
}

impl fmt::Display for Program<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        HirPrinter::to_string(|p| p.print_program(self)).fmt(f)
    }
}

impl fmt::Display for Expr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        HirPrinter::to_string(|p| p.print_expr(self)).fmt(f)
    }
}

impl fmt::Display for Pat<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        HirPrinter::to_string(|p| p.print_pat(self)).fmt(f)
    }
}

impl fmt::Display for Ty<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        HirPrinter::to_string(|p| p.print_type(*self, TypePrec::Top)).fmt(f)
    }
}

#[derive(Default)]
struct HirPrinter {
    pp: Printer,
}

impl Deref for HirPrinter {
    type Target = Printer;

    fn deref(&self) -> &Self::Target {
        &self.pp
    }
}

impl DerefMut for HirPrinter {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.pp
    }
}

impl PrintState for HirPrinter {}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd)]
enum TypePrec {
    Top,
    Arg,
}

impl HirPrinter {
    fn to_string<F>(f: F) -> String
    where
        F: FnOnce(&mut Self),
    {
        let mut printer = Self::default();
        f(&mut printer);
        printer.pp.eof()
    }

    fn print_program(&mut self, program: &Program<'_>) {
        self.print_comp_unit(program.unit);
        self.hardbreak();
        self.word("main = ");
        self.print_expr(program.main);
    }

    fn print_comp_unit(&mut self, unit: &CompUnit<'_>) {
        self.print_items(unit.items);
    }

    fn print_items(&mut self, items: &Items) {
        self.pp.cbox(INDENT);
        self.word("values [");
        //self.word(items.values.iter().format(",").to_string());
        self.word("]");
        self.pp.end();
    }

    fn print_pat(&mut self, pat: &Pat<'_>) {
        match pat.kind {
            PatKind::Wild => self.word("_"),
            PatKind::Lit(l) => self.print_lit(l),
            PatKind::Var(p) => self.print_path(p),
            PatKind::Ann(p, t) => {
                self.popen();
                self.print_pat(p);
                self.space();
                self.word_space(":");
                self.print_type(t, TypePrec::Top);
                self.pclose();
            }
            PatKind::Tuple(ps) => {
                self.popen();
                self.strsep(",", false, Breaks::Inconsistent, ps, |pp, p| {
                    pp.print_pat(p)
                });
                self.pclose();
            }
            PatKind::Constructor(cons, ps) => {
                if ps.is_empty() {
                    self.print_path(cons);
                } else {
                    self.word("(");
                    self.print_path(cons);
                    self.space();
                    self.strsep("", false, Breaks::Inconsistent, ps, |pp, p| pp.print_pat(p));
                    self.word(")");
                }
            }
            PatKind::Or(ps) => {
                self.strsep("|", true, Breaks::Inconsistent, ps, |pp, p| pp.print_pat(p))
            }
        }
    }

    fn print_arrow(&mut self, typ: Ty<'_>) {
        if let TyKind::Arrow(u, arg, ret) = *typ.kind() {
            self.print_type(arg, TypePrec::Arg);
            self.space();
            self.word("->");
            if u != NO_WEB {
                self.word(u.to_string());
            }
            self.space();
            self.print_arrow(ret);
        } else {
            self.print_type(typ, TypePrec::Top);
        }
    }

    fn print_type(&mut self, typ: Ty<'_>, prec: TypePrec) {
        match *typ.kind() {
            TyKind::Base(b) => self.word(b.to_string()),
            TyKind::Uni(v) => self.word(v.to_string()),
            TyKind::Var(v) => self.word(v.to_string()),
            TyKind::Skolem(v) => self.word(v.to_string()),
            TyKind::Arrow(..) => {
                prec.enclose(TypePrec::Arg, "(", ")", self, &typ, |pp, t| {
                    pp.print_arrow(*t)
                });
            }
            TyKind::Tuple(ts) => {
                self.popen();
                self.strsep(",", false, Breaks::Inconsistent, ts, |pp, t| {
                    pp.print_type(*t, TypePrec::Top)
                });
                self.pclose();
            }
            TyKind::Vector(t) => {
                self.word("[");
                self.print_type(t, TypePrec::Top);
                self.word("]");
            }
            TyKind::Row(..) => todo!("print rows"),
            TyKind::App(h, ts) => {
                prec.enclose(TypePrec::Arg, "(", ")", self, &(h, ts), |pp, (h, ts)| {
                    pp.print_path(*h);
                    pp.space();
                    pp.strsep("", false, Breaks::Inconsistent, ts, |pp, t| {
                        pp.print_type(*t, TypePrec::Arg)
                    });
                });
            }
        }
    }

    fn print_lit(&mut self, lit: Lit) {
        self.word(lit.to_string());
    }

    fn print_ident(&mut self, id: Ident) {
        self.word(id.to_string());
    }

    fn print_path(&mut self, path: Path<'_>) {
        self.word(path.to_string());
    }

    fn print_hir_id(&mut self, hir_id: HirId) {
        self.word(hir_id.to_string());
    }

    fn print_expr(&mut self, expr: &Expr<'_>) {
        self.ibox(INDENT);
        match expr.kind {
            ExprKind::Path(p) => self.print_path(p),
            ExprKind::Constructor(p) => self.print_path(p),
            ExprKind::Lit(l) => self.print_lit(l),
            ExprKind::Ann(e, t) => {
                self.popen();
                self.print_expr(e);
                self.space();
                self.word_space(":");
                self.print_type(t, TypePrec::Top);
                self.pclose();
            }
            ExprKind::Tuple(es) => {
                self.popen();
                self.strsep(",", false, Breaks::Inconsistent, es, |pp, e| {
                    pp.print_expr(e)
                });
                self.pclose();
            }
            ExprKind::Vector(es) => {
                self.word("[");
                self.strsep(",", false, Breaks::Inconsistent, es, |pp, e| {
                    pp.print_expr(e)
                });
                self.word("]");
            }
            ExprKind::Lambda(l) => self.print_lambda(l),
            ExprKind::Let(binds, body) => {
                self.word_space("let");
                let (first, rest) = binds.split_first().unwrap();
                self.print_bind(first);
                for bind in rest.iter() {
                    self.word_space(",");
                    self.print_bind(bind);
                }
                self.space();
                self.word_space("in");
                self.break_offset_if_not_bol(1, -INDENT);
                self.print_expr(body);
            }
            ExprKind::Call(_u, e, args) => {
                self.popen();
                self.print_expr(e);
                self.space();
                self.strsep("", false, Breaks::Inconsistent, args, |pp, arg| {
                    pp.print_expr(arg)
                });
                self.pclose();
            }
            ExprKind::Case(e, arms) => {
                self.cbox(0);
                self.ibox(0);
                self.word_nbsp("case");
                self.print_expr(e);
                self.space();
                self.word("{");
                self.end();
                for arm in arms {
                    self.print_arm(arm);
                }
                self.break_offset_if_not_bol(1, -INDENT);
                self.word("}");
                self.end();
            }
            _ => (),
        }
        self.end();
    }

    fn print_bind(&mut self, (pat, expr): &(Pat<'_>, Expr<'_>)) {
        self.print_pat(pat);
        self.space();
        self.word_space("=");
        self.print_expr(expr);
    }

    fn print_arm(&mut self, (pat, expr): &(Pat<'_>, Expr<'_>)) {
        self.space();
        self.cbox(INDENT);
        self.ibox(0);
        self.print_pat(pat);
        self.space();
        self.word_space("=>");
        self.print_expr(expr);
        self.end();
        self.word(",");
        self.end();
    }

    fn print_lambda(&mut self, lambda: &Lambda<'_>) {
        self.popen();
        self.word("\\");
        self.strsep("", false, Breaks::Inconsistent, lambda.args, |pp, p| {
            pp.print_pat(p)
        });
        self.space();
        self.word_space("->");
        self.print_expr(lambda.body);
        self.pclose();
    }
}
