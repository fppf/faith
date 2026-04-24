use base::hash::IndexMap;

use crate::{ExprId, ExprKind, Func, Join, MirCtxt, Program, Rhs, Var, free_vars};

pub fn shrink(program: &mut Program) {
    let mut shrinker = Shrinker::default();

    for func in &program.funcs {
        shrinker.shrink_func(&program.ctxt, func);
    }
    shrinker.shrink_expr(&program.ctxt, program.main);

    shrinker.compact(program);
}

#[derive(Default)]
struct Shrinker {
    replacements: IndexMap<ExprId, ExprId>,
}

impl Shrinker {
    fn compact(self, program: &mut Program) {
        for (from, to) in self.replacements {
            log::trace!("replace {from:?} with {to:?}");
            let replace_expr = program.ctxt.exprs.remove(to).unwrap();
            let _ = std::mem::replace(&mut program.ctxt.exprs[from], replace_expr);
        }
    }

    fn shrink_func(&mut self, ctxt: &MirCtxt, func: &Func) {
        self.shrink_expr(ctxt, func.body);
    }

    fn shrink_join(&mut self, ctxt: &MirCtxt, join: &Join) {
        self.shrink_expr(ctxt, join.body);
    }

    fn shrink_expr(&mut self, ctxt: &MirCtxt, expr_id: ExprId) {
        let expr = &ctxt.exprs[expr_id];

        match &expr.kind {
            ExprKind::Let { body, .. } => self.shrink_expr(ctxt, *body),
            ExprKind::LetFunc { func, body } => {
                self.shrink_func(ctxt, func);
                self.shrink_expr(ctxt, *body);
            }
            ExprKind::LetJoin { join, body } => {
                self.shrink_join(ctxt, join);
                self.shrink_expr(ctxt, *body);
            }
            ExprKind::Case(_, arms) => {
                for &(_, expr) in arms {
                    self.shrink_expr(ctxt, expr);
                }
            }
            ExprKind::Tail(_) | ExprKind::Jump(..) | ExprKind::Return(_) => (),
        }

        match &expr.kind {
            ExprKind::Let { lhs, rhs, body } if !matches!(rhs, Rhs::Call(_)) => {
                // Cannot remove calls on rhs, as they might not terminate
                self.try_replace(ctxt, *lhs, expr_id, *body);
            }
            ExprKind::LetFunc { func, body } => {
                self.try_replace(ctxt, func.name, expr_id, *body);
            }
            _ => (),
        }
    }

    fn try_replace(&mut self, ctxt: &MirCtxt, var: Var, enclosing: ExprId, enclosed: ExprId) {
        let mut check_inside = enclosed;
        if let Some(replacement) = self.replacements.get(&enclosed) {
            check_inside = *replacement;
        }
        if !free_vars(ctxt, check_inside).contains(&var) {
            self.replacements.insert(enclosing, enclosed);
        }
    }
}
