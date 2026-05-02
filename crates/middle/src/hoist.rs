use base::hash::IndexMap;

use crate::mir::{
    Expr, ExprId, ExprKind, Func, FuncId, JoinId, MirCtxt, Program, Value, Var, free_vars,
};

pub(crate) fn hoist(program: &mut Program) {
    let mut hoister = Hoister {
        ctxt: &mut program.ctxt,
        converted_joins: IndexMap::default(),
    };

    for func in &program.funcs {
        hoister.hoist_in_func(*func, None);
    }
    hoister.hoist_in_expr(program.main);

    hoister.rewrite_jumps();

    program.joins.extend(hoister.converted_joins.keys());
}

struct Hoister<'a> {
    ctxt: &'a mut MirCtxt,
    converted_joins: IndexMap<JoinId, Vec<Var>>,
}

impl<'a> Hoister<'a> {
    fn rewrite_jumps(&mut self) {
        for expr in self.ctxt.exprs.values_mut() {
            if let ExprKind::Jump(jump_id, args) = &mut expr.kind {
                let extra_args = self.converted_joins.get(jump_id).unwrap();
                args.extend(extra_args.iter().map(|&var| Value::Var(var)));
            }
        }
    }

    fn hoist_in_func(&mut self, func_id: FuncId, in_body: Option<ExprId>) {
        let func = std::mem::replace(&mut self.ctxt.funcs[func_id], Func::sentinel());

        if let Some(body_id) = in_body {
            self.hoist_in_expr(body_id);
        }

        self.hoist_in_expr(func.body);

        self.ctxt.funcs[func_id] = func;
    }

    fn hoist_in_expr(&mut self, expr_id: ExprId) {
        let expr = std::mem::replace(&mut self.ctxt.exprs[expr_id], Expr::SENTINEL);

        match &expr.kind {
            ExprKind::LetFunc { func_id, body } => {
                self.hoist_in_func(*func_id, Some(*body));
            }
            ExprKind::Let {
                lhs: _,
                rhs: _,
                body: body_id,
            } => {
                self.hoist_in_expr(*body_id);
            }
            ExprKind::LetJoin { join_id, body } => {
                let join_body = std::mem::replace(&mut self.ctxt.joins[*join_id].body, *body);
                let mut join_args =
                    std::mem::replace(&mut self.ctxt.joins[*join_id].args, Vec::new());
                self.hoist_in_expr(join_body);

                let mut fv = free_vars(self.ctxt, *body);
                for arg in &join_args {
                    fv.swap_remove(arg);
                }
                let fv: Vec<_> = fv.into_iter().collect();
                join_args.extend(fv.clone());

                self.converted_joins.insert(*join_id, fv);

                self.ctxt.joins[*join_id].args = join_args;
                self.ctxt.joins[*join_id].body = join_body;

                self.hoist_in_expr(*body);

                self.ctxt.exprs[expr_id] = self.ctxt.exprs.remove(*body).unwrap();
                return;
            }
            ExprKind::Case(_, items) => {
                for &(_, expr_id) in items {
                    self.hoist_in_expr(expr_id);
                }
            }
            ExprKind::Tail(_)
            | ExprKind::ExternalCall(..)
            | ExprKind::Jump(..)
            | ExprKind::Return(_) => (),
        }

        self.ctxt.exprs[expr_id] = expr;
    }
}
