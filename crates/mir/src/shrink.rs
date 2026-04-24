use crate::{Expr, ExprKind, Func, MirVisitor, Program, Rhs};

pub fn shrink(program: &mut Program) {
    let mut shrinker = Shrinker {};
    shrinker.visit_program(program);
}

struct Shrinker {}

impl MirVisitor for Shrinker {
    fn visit_expr(&mut self, expr: &mut Expr) {
        expr.walk(self);

        match &expr.kind {
            ExprKind::Let { lhs, rhs, body } => {
                // Cannot remove calls on rhs, as they might not terminate
                if !matches!(rhs, Rhs::Call(_)) {
                    let fv = body.free_vars();
                    if !fv.contains(&lhs) {
                        *expr = *body.clone();
                    }
                }
            }
            ExprKind::LetFunc { func, body } => {
                let fv = body.free_vars();
                if !fv.contains(&func.name) {
                    *expr = *body.clone();
                }
            }
            _ => (),
        }
    }
}
