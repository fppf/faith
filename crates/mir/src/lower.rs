use std::collections::VecDeque;

use base::{hash::Map, index::Idx};
use infer::{
    Res, ResId, hir,
    ty::{Ty, TyCtxt},
};
use span::{Ident, Sp, Span, Sym};

use crate::{Func, Join, JoinId, Value, Var, mir};

pub fn lower<'a, 't>(ctxt: &'t TyCtxt<'t>, program: &'a hir::Program<'t>) -> mir::Program {
    LoweringContext::new(ctxt, program).lower()
}

pub(crate) struct LoweringContext<'a, 't> {
    ctxt: &'t TyCtxt<'t>,
    program: &'a hir::Program<'t>,
    funcs: Vec<mir::Func>,
    res_to_var: Map<Res, Var>,
    var_to_res: Map<Var, Res>,
    temporaries: Map<Ident, Var>,
    stamp: u32,
}

enum Ctx<'a, 't> {
    Ret,
    Jump(JoinId),
    If(&'a hir::Expr<'t>, &'a hir::Expr<'t>, Box<Ctx<'a, 't>>),
    Case(&'a [(hir::Pat<'t>, hir::Expr<'t>)], Box<Ctx<'a, 't>>),
    List(
        ListKind,
        &'a [hir::Expr<'t>],
        usize,
        Vec<mir::Value>,
        Box<Ctx<'a, 't>>,
    ),
    Let(
        &'a [(hir::Pat<'t>, hir::Expr<'t>)],
        usize,
        &'a hir::Expr<'t>,
        Box<Ctx<'a, 't>>,
    ),
    Lambda(
        &'a [hir::Pat<'t>],
        Vec<(usize, hir::Var<'t>)>,
        usize,
        &'a hir::Expr<'t>,
        Box<Ctx<'a, 't>>,
    ),
    Seq(&'a hir::Expr<'t>, Box<Ctx<'a, 't>>),
}

enum ListKind {
    Call,
    Tuple,
    Vector,
}

impl<'a, 't> LoweringContext<'a, 't> {
    fn new(ctxt: &'t TyCtxt<'t>, program: &'a hir::Program<'t>) -> Self {
        Self {
            ctxt,
            program,
            funcs: Vec::new(),
            res_to_var: Map::default(),
            var_to_res: Map::default(),
            temporaries: Map::default(),
            stamp: 1,
        }
    }

    fn next_stamp(&mut self) -> u32 {
        let stamp = self.stamp;
        self.stamp += 1;
        stamp
    }

    fn get_or_insert_var(&mut self, var: hir::Var<'t>) -> mir::Var {
        let res = var.res;
        match self.res_to_var.get(&res) {
            Some(var) => *var,
            None => {
                let var = mir::Var::new(var.id.sym, self.next_stamp());
                self.res_to_var.insert(res, var);
                self.var_to_res.insert(var, res);
                var
            }
        }
    }

    pub fn get_var(&self, var: hir::Var<'t>) -> mir::Var {
        if var.res == Res::dummy() {
            return self.temporaries[&var.id];
        }
        *self
            .res_to_var
            .get(&var.res)
            .unwrap_or_else(|| panic!("res_to_var missing {var}"))
    }

    pub fn insert_var(&mut self, name: &str) -> (hir::Var<'t>, mir::Var) {
        let mir_var = mir::Var::new(Sym::intern(&format!("~{name}")), self.next_stamp());
        let id = Ident::new(mir_var.sym, Span::dummy());
        let hir_var = hir::Var::new(id, Res::dummy(), id.span);
        self.temporaries.insert(id, mir_var);
        let expr = hir::Expr::new(hir::ExprKind::Var(hir_var), Span::dummy());
        (hir_var, mir_var)
    }

    fn lower(mut self) -> mir::Program {
        for adt in self.ctxt.adts.borrow().values() {
            for cons in adt.constructors.values() {
                self.get_or_insert_var(cons.var);
            }
        }
        for import in self.program.imports.values() {
            self.lower_comp_unit(import);
        }
        self.lower_comp_unit(&self.program.unit);
        let main = self.lower_expr(&self.program.main);
        mir::Program {
            funcs: self.funcs,
            main,
        }
    }

    fn lower_comp_unit(&mut self, unit: &'a hir::CompUnit<'t>) {
        self.lower_items(&unit.items);
    }

    fn lower_items(&mut self, items: &'a [hir::Item<'t>]) {
        for item in items {
            match item {
                hir::Item::Expr {
                    var,
                    expr,
                    recursive,
                    ..
                } => {
                    let name = self.get_or_insert_var(*var);
                    let body = self.lower_expr(expr);
                    let func = mir::Func {
                        name,
                        args: vec![],
                        body: Box::new(body),
                        recursive: *recursive,
                    };
                    self.funcs.push(func);
                }
            }
        }
    }

    fn lower_lit(&self, lit: hir::Lit) -> mir::Lit {
        match lit {
            hir::Lit::Unit => mir::Lit::Unit,
            hir::Lit::Bool(b) => mir::Lit::Bool(b),
            hir::Lit::Int32(s) =>
            {
                #[allow(clippy::from_str_radix_10)]
                mir::Lit::Int32(i32::from_str_radix(&s.as_str().replace("_", ""), 10).unwrap())
            }
            hir::Lit::Str(s) => mir::Lit::Str(s),
        }
    }

    fn lower_expr(&mut self, expr: &'a hir::Expr<'t>) -> mir::Expr {
        self.lower_expr_ctx(expr, Ctx::Ret)
    }

    fn lower_var_ctx(&mut self, var: hir::Var<'t>, ctx: Ctx<'a, 't>) -> mir::Expr {
        let var = self.get_var(var);
        self.lower_expr_ret(Value::Var(var), ctx)
    }

    fn lower_expr_ctx(&mut self, expr: &'a hir::Expr<'t>, ctx: Ctx<'a, 't>) -> mir::Expr {
        use hir::ExprKind;
        match &expr.kind {
            ExprKind::Var(var) => self.lower_var_ctx(*var, ctx),
            ExprKind::Lit(lit) => {
                let lit = self.lower_lit(*lit);
                self.lower_expr_ret(Value::Lit(lit), ctx)
            }
            ExprKind::Ann(e, _) => self.lower_expr_ctx(e, ctx),
            ExprKind::If(cond, e1, e2) => self.lower_expr_ctx(cond, Ctx::If(e1, e2, Box::new(ctx))),
            ExprKind::Case(e, arms, _tree) => {
                self.lower_expr_ctx(e, Ctx::Case(&arms, Box::new(ctx)))
            }
            ExprKind::Tuple(es) => {
                assert!(!es.is_empty());
                self.lower_expr_ctx(
                    &es[0],
                    Ctx::List(ListKind::Tuple, &es, 1, Vec::new(), Box::new(ctx)),
                )
            }
            ExprKind::Vector(es) => {
                if !es.is_empty() {
                    self.lower_expr_ctx(
                        &es[0],
                        Ctx::List(ListKind::Vector, &es, 1, Vec::new(), Box::new(ctx)),
                    )
                } else {
                    self.lower_expr_ret(Value::Lit(mir::Lit::EmptyVector), ctx)
                }
            }
            ExprKind::Call(f, args) => self.lower_expr_ctx(
                f,
                Ctx::List(ListKind::Call, &args, 0, Vec::new(), Box::new(ctx)),
            ),
            ExprKind::Lambda(lambda) => {
                let (_, func_var) = self.insert_var("f");
                let mut args = Vec::with_capacity(lambda.args.len());
                let mut binds = Vec::new();
                for (i, arg) in lambda.args.iter().enumerate() {
                    let var = self.acc_lambda_binds(i, arg, &mut binds);
                    args.push(var);
                }
                // \p1 .. pn -> e ~>
                //   \l1 .. ln -> lower(let p1 = l1, .., pn = ln in e)
                let body = if binds.is_empty() {
                    self.lower_expr(&lambda.body)
                } else {
                    self.lower_var_ctx(
                        binds[0].1,
                        Ctx::Lambda(&lambda.args, binds, 1, &lambda.body, Box::new(Ctx::Ret)),
                    )
                };
                let func = mir::Func {
                    name: func_var,
                    args,
                    body: Box::new(body),
                    recursive: false,
                };
                mir::Expr::new(mir::ExprKind::LetFunc {
                    func,
                    body: Box::new(self.lower_expr_ret(Value::Var(func_var), ctx)),
                })
            }
            ExprKind::Let(binds, body) => {
                assert!(!binds.is_empty());
                self.lower_expr_ctx(&binds[0].1, Ctx::Let(binds, 1, body, Box::new(ctx)))
            }
            ExprKind::Seq(e1, e2) => self.lower_expr_ctx(&e1, Ctx::Seq(&e2, Box::new(ctx))),
        }
    }

    fn acc_lambda_binds(
        &mut self,
        idx: usize,
        pat: &'a hir::Pat<'t>,
        binds: &mut Vec<(usize, hir::Var<'t>)>,
    ) -> mir::Var {
        use hir::PatKind;
        match &pat.kind {
            PatKind::Wild => self.insert_var("w").1,
            PatKind::Var(v) => self.get_or_insert_var(*v),
            PatKind::Tuple(_) => {
                let (temp, var) = self.insert_var("tup");
                binds.push((idx, temp));
                var
            }
            PatKind::Ann(p, _) => self.acc_lambda_binds(idx, p, binds),
            PatKind::Lit(_) => panic!("literal pattern as lambda argument"),
            PatKind::Or(_) => panic!("or pattern as lambda argument"),
            PatKind::Cons(..) => {
                panic!("constructor pattern as lambda argument")
            }
        }
    }

    fn lower_expr_ret(&mut self, value: Value, mut ctx: Ctx<'a, 't>) -> mir::Expr {
        match ctx {
            Ctx::Ret => mir::Expr::new(mir::ExprKind::Return(value)),
            Ctx::Jump(join_id) => mir::Expr::new(mir::ExprKind::Jump(join_id, vec![value])),
            Ctx::If(e1, e2, ctx) => {
                let join_id = JoinId(self.next_stamp());
                let (_, join_arg) = self.insert_var("p");
                let join = Join {
                    id: join_id,
                    args: vec![join_arg],
                    body: Box::new(self.lower_expr_ret(Value::Var(join_arg), *ctx)),
                };
                let e1 = self.lower_expr_ctx(e1, Ctx::Jump(join_id));
                let e2 = self.lower_expr_ctx(e2, Ctx::Jump(join_id));
                mir::Expr::new(mir::ExprKind::LetJoin {
                    join,
                    body: Box::new(mir::Expr::new(mir::ExprKind::Case(
                        value,
                        vec![
                            (mir::Pat::Lit(mir::Lit::Bool(true)), e1),
                            (mir::Pat::Lit(mir::Lit::Bool(false)), e2),
                        ],
                    ))),
                })
            }
            Ctx::Case(arms, ctx) => {
                let join_id = JoinId(self.next_stamp());
                let (_, join_arg) = self.insert_var("p");
                let join = Join {
                    id: join_id,
                    args: vec![join_arg],
                    body: Box::new(self.lower_expr_ret(Value::Var(join_arg), *ctx)),
                };
                let mut lowered_arms = Vec::new();
                for (pat, expr) in arms {
                    //let pat = todo!();
                    //let expr = self.lower_expr_ctx(expr, Ctx::Jump(join_id));
                    //lowered_arms.push((pat, expr));
                }
                mir::Expr::new(mir::ExprKind::LetJoin {
                    join,
                    body: Box::new(mir::Expr::new(mir::ExprKind::Case(value, lowered_arms))),
                })
            }
            Ctx::List(kind, exprs, index, mut values, ctx) => {
                values.push(value);
                if index == exprs.len() {
                    let (_, tmp) = self.insert_var("t");
                    let rhs = match kind {
                        ListKind::Call => {
                            let (func, args) = values.split_first().unwrap();
                            let func = match func {
                                Value::Var(var) => *var,
                                Value::External(s) => todo!(),
                                Value::Lit(_) => panic!("literal in function position"),
                            };
                            mir::Rhs::Call(mir::Call {
                                func,
                                args: args.into(),
                            })
                        }
                        ListKind::Tuple => mir::Rhs::Tuple(values),
                        ListKind::Vector => mir::Rhs::Vector(values),
                    };
                    mir::Expr::new(mir::ExprKind::Let {
                        lhs: tmp,
                        rhs,
                        body: Box::new(self.lower_expr_ret(Value::Var(tmp), *ctx)),
                    })
                } else {
                    self.lower_expr_ctx(
                        &exprs[index],
                        Ctx::List(kind, exprs, index + 1, values, ctx),
                    )
                }
            }
            Ctx::Let(binds, index, body, ctx) => {
                let (pat, expr) = &binds[index - 1];
                let (_, mut tmp) = self.insert_var("t");
                let lowered_binds = match pat.kind {
                    hir::PatKind::Var(id) => {
                        tmp = self.get_or_insert_var(id);
                        Vec::new()
                    }
                    _ => self.lower_bind(pat, 0, tmp),
                };
                let body = if index == binds.len() {
                    self.lower_expr_ctx(body, *ctx)
                } else {
                    self.lower_expr_ctx(expr, Ctx::Let(binds, index + 1, body, ctx))
                };
                let body = if lowered_binds.is_empty() {
                    body
                } else {
                    lowered_binds
                        .into_iter()
                        .rev()
                        .fold(body, |acc, (lhs, rhs, i)| {
                            mir::Expr::new(mir::ExprKind::Let {
                                lhs,
                                rhs: if i > 0 {
                                    mir::Rhs::Proj(rhs, i - 1)
                                } else {
                                    mir::Rhs::Value(Value::Var(rhs))
                                },
                                body: Box::new(acc),
                            })
                        })
                };
                mir::Expr::new(mir::ExprKind::Let {
                    lhs: tmp,
                    rhs: mir::Rhs::Value(value),
                    body: Box::new(body),
                })
            }
            Ctx::Lambda(args, binds, index, body, ctx) => {
                let (i, var) = &binds[index - 1];
                let pat = &args[*i];
                let (_, mut tmp) = self.insert_var("t");
                let lowered_binds = match pat.kind {
                    hir::PatKind::Var(id) => {
                        tmp = self.get_or_insert_var(id);
                        Vec::new()
                    }
                    _ => self.lower_bind(pat, 0, tmp),
                };
                let body = if index == binds.len() {
                    self.lower_expr_ctx(body, *ctx)
                } else {
                    self.lower_var_ctx(*var, Ctx::Lambda(args, binds, index + 1, body, ctx))
                };
                let body = if lowered_binds.is_empty() {
                    body
                } else {
                    lowered_binds
                        .into_iter()
                        .rev()
                        .fold(body, |acc, (lhs, rhs, i)| {
                            mir::Expr::new(mir::ExprKind::Let {
                                lhs,
                                rhs: if i > 0 {
                                    mir::Rhs::Proj(rhs, i - 1)
                                } else {
                                    mir::Rhs::Value(Value::Var(rhs))
                                },
                                body: Box::new(acc),
                            })
                        })
                };
                mir::Expr::new(mir::ExprKind::Let {
                    lhs: tmp,
                    rhs: mir::Rhs::Value(value),
                    body: Box::new(body),
                })
            }

            Ctx::Seq(e2, ctx) => {
                let (_, unused) = self.insert_var("seq");
                let e2 = self.lower_expr_ctx(e2, *ctx);
                mir::Expr::new(mir::ExprKind::Let {
                    lhs: unused,
                    rhs: mir::Rhs::Value(value),
                    body: Box::new(e2),
                })
            }
        }
    }

    fn lower_bind(
        &mut self,
        pat: &'a hir::Pat<'t>,
        index: usize,
        var: Var,
    ) -> Vec<(Var, Var, usize)> {
        use hir::PatKind;
        match &pat.kind {
            PatKind::Lit(_) => panic!("literal pattern as LHS of bind"),
            PatKind::Wild => {
                let (_, unused) = self.insert_var("w");
                vec![(unused, var, index)]
            }
            PatKind::Var(v) => {
                vec![(self.get_or_insert_var(*v), var, index)]
            }
            PatKind::Ann(p, _) => self.lower_bind(p, index, var),
            PatKind::Tuple(ps) => {
                let mut binds = Vec::new();
                let mut rhs_var = var;
                if index > 0 {
                    let (_, new_var) = self.insert_var("tup");
                    binds.push((new_var, var, index));
                    rhs_var = new_var;
                }
                for (i, p) in ps.iter().enumerate() {
                    binds.extend(self.lower_bind(p, i + 1, rhs_var));
                }
                binds
            }
            PatKind::Cons(..) => {
                // We could allow this when the pattern is irrefutable,
                // i.e., only one constructor for the ADT.
                todo!("implement irrefutable pattern destructuring")
            }
            PatKind::Or(_) => todo!("implement or patterns"),
        }
    }
}
