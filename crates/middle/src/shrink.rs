use crate::mir::{Expr, ExprId, ExprKind, FuncId, MirCtxt, Program, Rhs, Var, free_vars};

pub(crate) fn shrink(program: &mut Program) {
    let mut shrinker = Shrinker::default();

    for func in &program.funcs {
        shrinker.shrink_func(&mut program.ctxt, *func);
    }
    shrinker.shrink_expr(&mut program.ctxt, program.main);
}

#[derive(Default)]
struct Shrinker {}

impl Shrinker {
    fn shrink_func(&mut self, ctxt: &mut MirCtxt, func_id: FuncId) {
        let func = &ctxt.funcs[func_id];
        self.shrink_expr(ctxt, func.body);
    }

    fn shrink_expr(&mut self, ctxt: &mut MirCtxt, expr_id: ExprId) {
        let expr = std::mem::replace(&mut ctxt.exprs[expr_id], Expr::SENTINEL);

        match &expr.kind {
            ExprKind::Let { body, .. } => self.shrink_expr(ctxt, *body),
            ExprKind::LetFunc { func, body } => {
                self.shrink_func(ctxt, *func);
                self.shrink_expr(ctxt, *body);
            }
            ExprKind::LetJoin { join, body } => {
                self.shrink_expr(ctxt, join.body);
                self.shrink_expr(ctxt, *body);
            }
            ExprKind::Case(_, arms) => {
                for &(_, expr) in arms {
                    self.shrink_expr(ctxt, expr);
                }
            }
            ExprKind::Tail(_) | ExprKind::Jump(..) | ExprKind::Return(_) => (),
        }

        let modified = match &expr.kind {
            ExprKind::Let { lhs, rhs, body } if !matches!(rhs, Rhs::Call(_)) => {
                // Cannot remove calls on rhs, as they might not terminate
                self.try_replace(ctxt, *lhs, expr_id, *body)
            }
            ExprKind::LetFunc { func, body } => {
                let func = &ctxt.funcs[*func];
                self.try_replace(ctxt, func.name, expr_id, *body)
            }
            _ => false,
        };

        if !modified {
            ctxt.exprs[expr_id] = expr;
        }
    }

    fn try_replace(
        &mut self,
        ctxt: &mut MirCtxt,
        var: Var,
        enclosing: ExprId,
        enclosed: ExprId,
    ) -> bool {
        if !free_vars(ctxt, enclosed).contains(&var) {
            ctxt.exprs[enclosing] = ctxt.exprs.remove(enclosed).unwrap();
            true
        } else {
            false
        }
    }
}
