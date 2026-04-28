use base::hash::IndexSet;
use span::Sym;

use crate::mir::{
    Call, Expr, ExprId, ExprKind, Func, FuncId, MirCtxt, Program, Rhs, Value, free_vars,
};

pub(crate) fn convert(program: &mut Program) {
    let mut converter = ClosureConvert::default();
    for func in &program.funcs {
        converter.convert_func(&mut program.ctxt, *func, None);
    }
    converter.convert_expr(&mut program.ctxt, program.main);

    program.funcs.extend(converter.hoisted);
}

#[derive(Default)]
struct ClosureConvert {
    hoisted: Vec<FuncId>,
}

impl ClosureConvert {
    fn convert_func(&mut self, ctxt: &mut MirCtxt, func_id: FuncId, in_body: Option<ExprId>) {
        let mut func = std::mem::replace(&mut ctxt.funcs[func_id], Func::sentinel());

        let args_set: IndexSet<_> = func.args.iter().copied().collect();

        let fv = free_vars(ctxt, func.body);
        let env: IndexSet<_> = fv.difference(&args_set).copied().collect();
        //log::trace!("fv: {:?}, args {:?}", fv, args_set);

        // Could avoid making env when env.is_empty()
        // Would require determining which callsites need to be modified

        let env_param_var = ctxt.new_var(Sym::intern("~env"));
        func.args.insert(0, env_param_var);

        let func_body = ctxt.exprs[func.body].clone();
        let func_body = ctxt.new_expr(func_body.kind);
        let replace_expr = env
            .iter()
            .enumerate()
            .rev()
            .fold(func_body, |acc, (i, &lhs)| {
                ctxt.new_expr(ExprKind::Let {
                    lhs,
                    rhs: Rhs::Proj(env_param_var, i + 1),
                    body: acc,
                })
            });
        ctxt.exprs[func.body] = ctxt.exprs.remove(replace_expr).unwrap();

        if let Some(body_id) = in_body {
            let body = ctxt.exprs[body_id].clone();
            let body = ctxt.new_expr(body.kind);

            let mut env_tuple = Vec::with_capacity(env.len() + 1);
            env_tuple.push(Value::Ptr(func.name));
            env_tuple.extend(env.iter().copied().map(|v| Value::Var(v)));

            let new_body = Expr::new(ExprKind::Let {
                lhs: func.name,
                rhs: Rhs::Tuple(env_tuple),
                body,
            });

            self.convert_expr(ctxt, body_id);
            ctxt.exprs[body_id] = new_body;
        }

        self.convert_expr(ctxt, func.body);

        ctxt.funcs[func_id] = func;

        self.hoisted.push(func_id);
    }

    fn convert_expr(&mut self, ctxt: &mut MirCtxt, expr_id: ExprId) {
        let expr = std::mem::replace(&mut ctxt.exprs[expr_id], Expr::SENTINEL);

        match &expr.kind {
            ExprKind::LetFunc { func, body } => {
                self.convert_func(ctxt, *func, Some(*body));
            }
            ExprKind::Let {
                lhs,
                rhs,
                body: body_id,
            } => {
                self.convert_expr(ctxt, *body_id);
                match rhs {
                    Rhs::Call(call_id) => {
                        // Given
                        //
                        //    let lhs = f args in body
                        //
                        // produce
                        //
                        //    let ~f_c = f.0 in
                        //    let lhs = ~f_c f args in
                        //    convert(body)
                        //

                        let call = ctxt.calls.remove(*call_id).unwrap();
                        let code_var =
                            ctxt.new_var(Sym::intern(&format!("~{}_c", call.func_var.sym)));
                        let mut args = vec![Value::Var(call.func_var)];
                        args.extend(call.args);
                        let new_call = ctxt.new_call(Call {
                            func_var: code_var,
                            args,
                        });

                        let new_let = ctxt.new_expr(ExprKind::Let {
                            lhs: *lhs,
                            rhs: Rhs::Call(new_call),
                            body: *body_id,
                        });

                        ctxt.exprs[expr_id] = Expr::new(ExprKind::Let {
                            lhs: code_var,
                            rhs: Rhs::Proj(call.func_var, 0),
                            body: new_let,
                        });

                        return;
                    }
                    _ => (),
                }
            }
            ExprKind::LetJoin { join: _, body } => {
                self.convert_expr(ctxt, *body);
            }
            ExprKind::Case(_, items) => {
                for &(_, expr_id) in items {
                    self.convert_expr(ctxt, expr_id);
                }
            }
            ExprKind::Tail(_call) => unreachable!(),
            ExprKind::Jump(..) | ExprKind::Return(_) => (),
        }

        ctxt.exprs[expr_id] = expr;
    }
}
