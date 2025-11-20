use std::collections::VecDeque;

use base::{hash::Map, index::Idx};
use infer::{Environment, Res, ResId, Resolution, ty::Ty};
use span::{Ident, Sp, Span, Sym};
use syntax::ast::{self, AstId, ExprKind, Item, PatKind};

use crate::{Func, Join, JoinId, Value, Var, mir};

pub fn lower<'ast, 't>(
    syntax_arena: &'ast syntax::Arena<'ast>,
    program: &'ast ast::Program<'ast>,
    resolution: &'t Resolution<'t>,
    environment: &'t Environment<'t>,
) -> mir::Program {
    LoweringContext::new(syntax_arena, program, resolution, environment).lower()
}

pub(crate) struct LoweringContext<'ast, 't> {
    funcs: Vec<mir::Func>,
    res_to_var: Map<ResId, Var>,
    var_to_res: Map<Var, ResId>,
    temporaries: Map<Ident, Var>,
    stamp: u32,
    program: &'ast ast::Program<'ast>,
    syntax_arena: &'ast syntax::Arena<'ast>,
    resolution: &'t Resolution<'t>,
    environment: &'t Environment<'t>,
}

enum Ctx<'ast> {
    Ret,
    Jump(JoinId),
    If(&'ast ast::Expr<'ast>, &'ast ast::Expr<'ast>, Box<Ctx<'ast>>),
    Case(&'ast [(ast::Pat<'ast>, ast::Expr<'ast>)], Box<Ctx<'ast>>),
    List(
        ListKind,
        &'ast [ast::Expr<'ast>],
        usize,
        Vec<Value>,
        Box<Ctx<'ast>>,
    ),
    Let(
        &'ast [(ast::Pat<'ast>, ast::Expr<'ast>)],
        usize,
        &'ast ast::Expr<'ast>,
        Box<Ctx<'ast>>,
    ),
    Seq(&'ast ast::Expr<'ast>, Box<Ctx<'ast>>),
}

enum ListKind {
    Call,
    Tuple,
    Vector,
}

impl<'ast, 't> LoweringContext<'ast, 't> {
    fn new(
        syntax_arena: &'ast syntax::Arena<'ast>,
        program: &'ast ast::Program<'ast>,
        resolution: &'t Resolution<'t>,
        environment: &'t Environment<'t>,
    ) -> Self {
        Self {
            funcs: Vec::new(),
            res_to_var: Map::default(),
            var_to_res: Map::default(),
            temporaries: Map::default(),
            stamp: 1,
            program,
            syntax_arena,
            resolution,
            environment,
        }
    }

    fn next_stamp(&mut self) -> u32 {
        let stamp = self.stamp;
        self.stamp += 1;
        stamp
    }

    fn get_or_insert_var(&mut self, id: ast::Id) -> Var {
        let res_id = self.resolution[id.ast_id].res_id();
        match self.res_to_var.get(&res_id) {
            Some(var) => *var,
            None => {
                let var = Var::new(id.ident.sym, self.next_stamp());
                self.res_to_var.insert(res_id, var);
                self.var_to_res.insert(var, res_id);
                var
            }
        }
    }

    pub fn get_var(&self, path: ast::Path<'ast>) -> Var {
        if path.ast_id == AstId::ZERO {
            let id = path.as_ident().unwrap();
            return self.temporaries[&id.ident];
        }
        let res = self.resolution[path.ast_id];
        self.res_to_var[&res.res_id()]
    }

    pub fn insert_var(&mut self, name: &str) -> (ast::Expr<'ast>, Var) {
        let var = Var::new(Sym::intern(&format!("~{name}")), self.next_stamp());
        let id = Ident::new(var.sym, Span::dummy());
        self.temporaries.insert(id, var);
        let expr = ast::Expr::new(
            ast::ExprKind::Path(ast::Path::new(id, &[], Span::dummy(), AstId::ZERO)),
            Span::dummy(),
            AstId::ZERO,
        );
        (expr, var)
    }

    fn lower(mut self) -> mir::Program {
        for (res_id, ctor) in &self.resolution.constructors {
            self.get_or_insert_var(ctor.id);
        }
        self.lower_comp_unit(self.program.unit);
        let main = self.lower_expr(self.program.main);
        mir::Program {
            funcs: self.funcs,
            main,
        }
    }

    fn lower_comp_unit(&mut self, unit: &'ast ast::CompUnit<'ast>) {
        self.lower_items(unit.items);
    }

    fn lower_mod_expr(&mut self, mexpr: &'ast Sp<ast::ModExpr<'ast>>) {
        match mexpr.value {
            ast::ModExpr::Path(_) => todo!(),
            ast::ModExpr::Import(source_id) => {
                let unit = self
                    .program
                    .imports
                    .get(&source_id)
                    .expect("invalid import");
                self.lower_comp_unit(unit);
            }
            ast::ModExpr::Struct(items) => self.lower_items(items),
        }
    }

    fn lower_items(&mut self, items: &'ast [Sp<Item<'ast>>]) {
        for item in items {
            match item.value {
                Item::Type(..) => (),
                Item::Value(id, _, expr) => {
                    let var = self.get_or_insert_var(id);
                    let body = self.lower_expr(expr);
                    let res = self.resolution[id.ast_id];
                    let value = self.resolution.values[&res.res_id()];
                    let func = mir::Func {
                        name: var,
                        args: vec![],
                        body: Box::new(body),
                        recursive: value.recursive,
                    };
                    self.funcs.push(func);
                }
                Item::Mod(_, mexpr) => self.lower_mod_expr(mexpr),
            }
        }
    }

    fn lower_lit(&self, lit: ast::Lit) -> mir::Lit {
        match lit {
            ast::Lit::Unit => mir::Lit::Unit,
            ast::Lit::Bool(b) => mir::Lit::Bool(b),
            ast::Lit::Int32(s) =>
            {
                #[allow(clippy::from_str_radix_10)]
                mir::Lit::Int32(i32::from_str_radix(&s.as_str().replace("_", ""), 10).unwrap())
            }
            ast::Lit::Str(s) => mir::Lit::Str(s),
        }
    }

    fn lower_expr(&mut self, expr: &'ast ast::Expr<'ast>) -> mir::Expr {
        self.lower_expr_ctx(expr, Ctx::Ret)
    }

    fn lower_expr_ctx(&mut self, expr: &'ast ast::Expr<'ast>, ctx: Ctx<'ast>) -> mir::Expr {
        match expr.kind {
            ExprKind::Path(path) => {
                let var = self.get_var(path);
                self.lower_expr_ret(Value::Var(var), ctx)
            }
            ExprKind::Cons(path) => {
                let var = self.get_var(path);
                self.lower_expr_ret(Value::Var(var), ctx)
            }
            ExprKind::External(s) => self.lower_expr_ret(Value::External(s.sym), ctx),
            ExprKind::Lit(lit) => {
                let lit = self.lower_lit(lit);
                self.lower_expr_ret(Value::Lit(lit), ctx)
            }
            ExprKind::Ann(e, _) => self.lower_expr_ctx(e, ctx),
            ExprKind::If(cond, e1, e2) => self.lower_expr_ctx(cond, Ctx::If(e1, e2, Box::new(ctx))),
            ExprKind::Case(e, arms) => self.lower_expr_ctx(e, Ctx::Case(arms, Box::new(ctx))),
            ExprKind::Tuple(es) => {
                assert!(!es.is_empty());
                self.lower_expr_ctx(
                    &es[0],
                    Ctx::List(ListKind::Tuple, es, 1, Vec::new(), Box::new(ctx)),
                )
            }
            ExprKind::Vector(es) => {
                if !es.is_empty() {
                    self.lower_expr_ctx(
                        &es[0],
                        Ctx::List(ListKind::Vector, es, 1, Vec::new(), Box::new(ctx)),
                    )
                } else {
                    self.lower_expr_ret(Value::Lit(mir::Lit::EmptyVector), ctx)
                }
            }
            ExprKind::Call(f, args) => self.lower_expr_ctx(
                f,
                Ctx::List(ListKind::Call, args, 0, Vec::new(), Box::new(ctx)),
            ),
            ExprKind::Lambda(lambda) => {
                let (_, func_var) = self.insert_var("f");
                let mut args = Vec::with_capacity(lambda.args.len());
                let mut binds = Vec::new();
                for &arg in lambda.args {
                    let var = self.acc_lambda_binds(arg, &mut binds);
                    args.push(var);
                }
                let body = if binds.is_empty() {
                    lambda.body
                } else {
                    // \p1 .. pn -> e ~>
                    //   \l1 .. ln -> lower(let p1 = l1, .., pn = ln in e)
                    self.syntax_arena.alloc(ast::Expr::new(
                        ast::ExprKind::Let(self.syntax_arena.alloc_from_iter(binds), lambda.body),
                        lambda.body.span,
                        AstId::ZERO,
                    ))
                };
                let body = self.lower_expr(body);
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
            ExprKind::Seq(e1, e2) => self.lower_expr_ctx(e1, Ctx::Seq(e2, Box::new(ctx))),
        }
    }

    fn acc_lambda_binds(
        &mut self,
        pat: ast::Pat<'ast>,
        binds: &mut Vec<(ast::Pat<'ast>, ast::Expr<'ast>)>,
    ) -> Var {
        match pat.kind {
            PatKind::Wild => self.insert_var("w").1,
            PatKind::Var(id) => self.get_or_insert_var(id),
            PatKind::Tuple(_) => {
                let (temp, var) = self.insert_var("tup");
                binds.push((pat, temp));
                var
            }
            PatKind::Ann(p, _) => self.acc_lambda_binds(*p, binds),
            PatKind::Lit(_) => panic!("literal pattern as lambda argument"),
            PatKind::Or(_) => panic!("or pattern as lambda argument"),
            PatKind::Cons(..) => {
                panic!("constructor pattern as lambda argument")
            }
        }
    }

    fn lower_expr_ret(&mut self, value: Value, mut ctx: Ctx<'ast>) -> mir::Expr {
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
                    let pat: mir::Pat = todo!("need to do pattern compilation");
                    let expr = self.lower_expr_ctx(expr, Ctx::Jump(join_id));
                    lowered_arms.push((pat, expr));
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
                    ast::PatKind::Var(id) => {
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
        pat: &'ast ast::Pat<'ast>,
        index: usize,
        var: Var,
    ) -> Vec<(Var, Var, usize)> {
        match pat.kind {
            PatKind::Lit(_) => panic!("literal pattern as LHS of bind"),
            PatKind::Wild => {
                let (_, unused) = self.insert_var("w");
                vec![(unused, var, index)]
            }
            PatKind::Var(id) => {
                vec![(self.get_or_insert_var(id), var, index)]
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
