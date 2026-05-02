use crate::mir::{Expr, ExprId, ExprKind, FuncId, MirCtxt, Program, Rhs, Var, free_vars};

pub(crate) fn shrink(program: &mut Program) {
    let mut shrinker = Shrinker {
        ctxt: &mut program.ctxt,
    };

    for func in &program.funcs {
        shrinker.shrink_func(*func);
    }
    shrinker.shrink_expr(program.main);
}

struct Shrinker<'a> {
    ctxt: &'a mut MirCtxt,
}

impl<'a> Shrinker<'a> {
    fn shrink_func(&mut self, func_id: FuncId) {
        let func = &self.ctxt.funcs[func_id];
        self.shrink_expr(func.body);
    }

    fn shrink_expr(&mut self, expr_id: ExprId) {
        let expr = std::mem::replace(&mut self.ctxt.exprs[expr_id], Expr::SENTINEL);

        match &expr.kind {
            ExprKind::Let { body, .. } => self.shrink_expr(*body),
            ExprKind::LetFunc { func_id, body } => {
                self.shrink_func(*func_id);
                self.shrink_expr(*body);
            }
            ExprKind::LetJoin { join_id, body } => {
                let join = &self.ctxt.joins[*join_id];
                self.shrink_expr(join.body);
                self.shrink_expr(*body);
            }
            ExprKind::Case(_, arms) => {
                for &(_, expr) in arms {
                    self.shrink_expr(expr);
                }
            }
            ExprKind::Tail(_)
            | ExprKind::ExternalCall(..)
            | ExprKind::Jump(..)
            | ExprKind::Return(_) => (),
        }

        let modified = match &expr.kind {
            ExprKind::Let { lhs, rhs, body } if !matches!(rhs, Rhs::Call(_)) => {
                // Cannot remove calls on rhs, as they might not terminate
                self.try_replace(*lhs, expr_id, *body)
            }
            ExprKind::LetFunc { func_id, body } => {
                let func = &self.ctxt.funcs[*func_id];
                self.try_replace(func.name, expr_id, *body)
            }
            _ => false,
        };

        if !modified {
            self.ctxt.exprs[expr_id] = expr;
        }
    }

    fn try_replace(&mut self, var: Var, enclosing: ExprId, enclosed: ExprId) -> bool {
        if !free_vars(self.ctxt, enclosed).contains(&var) {
            self.ctxt.exprs[enclosing] = self.ctxt.exprs.remove(enclosed).unwrap();
            true
        } else {
            false
        }
    }
}
