use std::{
    fmt,
    ops::{Deref, DerefMut},
};

use crate::{
    Lit, Value,
    mir::{Expr, Label, Module},
};

use base::pp::*;

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "l{}", Superscript(self.as_u32()))
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        MirPrinter::to_string(|p| p.print_expr(self)).fmt(f)
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        MirPrinter::to_string(|p| p.print_module(self)).fmt(f)
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

struct MirPrinter {
    pp: Printer,
}

impl Deref for MirPrinter {
    type Target = Printer;

    fn deref(&self) -> &Self::Target {
        &self.pp
    }
}

impl DerefMut for MirPrinter {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.pp
    }
}

impl PrintState for MirPrinter {}

impl MirPrinter {
    fn new() -> Self {
        MirPrinter {
            pp: Printer::default(),
        }
    }

    fn to_string<F>(f: F) -> String
    where
        F: FnOnce(&mut Self),
    {
        let mut printer = Self::new();
        f(&mut printer);
        printer.pp.eof()
    }

    fn print_label(&mut self, label: Label) {
        self.word(label.to_string());
    }

    fn print_value(&mut self, value: &Value) {
        match value {
            Value::Label(l) => self.print_label(*l),
            Value::Lit(l) => self.word(l.to_string()),
            Value::External(s) => {
                self.word("external");
                self.popen();
                self.word(s.as_str().to_string());
                self.pclose();
            }
        }
    }

    fn print_expr(&mut self, expr: &Expr) {
        self.ibox(INDENT);
        match expr {
            Expr::Value(v) => self.print_value(v),
            Expr::Tuple(vs) => {
                self.popen();
                self.strsep(",", false, Breaks::Inconsistent, vs, |pp, v| {
                    pp.print_value(v)
                });
                self.pclose();
            }
            Expr::Vector(vs) => {
                self.word("[");
                self.strsep(",", false, Breaks::Inconsistent, vs, |pp, v| {
                    pp.print_value(v)
                });
                self.word("]");
            }
            Expr::Let(l, e1, e2) => {
                self.word_space("let");
                self.print_label(*l);
                self.space();
                self.word_space("=");
                self.print_expr(e1);
                self.space();
                self.word("in");
                self.hardbreak();
                self.break_offset_if_not_bol(1, -INDENT);
                self.print_expr(e2);
            }
            Expr::Proj(l, i) => {
                self.print_label(*l);
                self.word(".");
                self.word(i.to_string());
            }
            Expr::Lambda(args, body) => {
                self.word("\\");
                self.strsep("", false, Breaks::Inconsistent, args, |pp, arg| {
                    pp.print_label(*arg)
                });
                self.space();
                self.word_space("->");
                self.print_expr(body);
            }
            Expr::Call(f, args) => {
                self.word("(");
                self.print_label(*f);
                self.space();
                self.strsep("", false, Breaks::Inconsistent, args, |pp, e| {
                    pp.print_value(e)
                });
                self.word(")");
            }
            Expr::Case(l, _tree) => {
                self.cbox(0);
                self.ibox(0);
                self.word_space("case");
                self.print_label(*l);
                self.space();
                self.word("{");
                self.word("}");
                self.end();
                self.end();
            }
            Expr::If(l, e1, e2) => {
                self.word("if ");
                self.print_label(*l);
                self.word(" then ");
                self.print_expr(e1);
                self.word(" else ");
                self.print_expr(e2);
            }
        }
        self.end();
    }

    fn print_module(&mut self, module: &Module) {
        for item in &module.items {
            self.word_space("val");
            self.print_label(item.label);
            self.space();
            self.word_space("=");
            self.cbox(INDENT);
            self.print_expr(&item.body);
            self.end();
            self.hardbreak();
        }
    }
}
