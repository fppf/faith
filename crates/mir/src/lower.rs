use base::{hash::Map, index::Idx};
use infer::{Environment, Res, ResId, Resolution, ty::Ty};
use span::{Ident, Sp, Span, Sym};
use syntax::ast::{self, AstId, ExprKind, Item, PatKind};

use crate::{
    MAIN_LABEL, Module, Value,
    mir::{self, Label},
};

pub fn lower<'ast, 't>(
    syntax_arena: &'ast syntax::Arena<'ast>,
    program: &'ast ast::Program<'ast>,
    resolution: &'t Resolution<'t>,
    environment: &'t Environment<'t>,
) -> mir::Module {
    LoweringContext::new(syntax_arena, program, resolution, environment).lower()
}

// TODO. clean up profanity of maps.
pub(crate) struct LoweringContext<'ast, 't> {
    module: mir::Module,
    res_to_label: Map<ResId, Label>,
    label_to_res: Map<Label, ResId>,
    label_to_type: Map<Label, Ty<'t>>,
    temporaries: Map<Ident, Label>,
    label: Label,
    program: &'ast ast::Program<'ast>,
    syntax_arena: &'ast syntax::Arena<'ast>,
    resolution: &'t Resolution<'t>,
    environment: &'t Environment<'t>,
}

impl<'ast, 't> LoweringContext<'ast, 't> {
    fn new(
        syntax_arena: &'ast syntax::Arena<'ast>,
        program: &'ast ast::Program<'ast>,
        resolution: &'t Resolution<'t>,
        environment: &'t Environment<'t>,
    ) -> Self {
        Self {
            module: Module::default(),
            res_to_label: Map::default(),
            label_to_res: Map::default(),
            label_to_type: Map::default(),
            temporaries: Map::default(),
            label: MAIN_LABEL.plus(1),
            program,
            syntax_arena,
            resolution,
            environment,
        }
    }

    fn next_label(&mut self) -> Label {
        let label = self.label;
        self.label = self.label + 1;
        label
    }

    pub fn insert_temp(&mut self) -> (&'ast ast::Expr<'ast>, Label) {
        let label = self.next_label();
        let id = Ident::new(
            Sym::intern(&format!("~tmp{}", label.index())),
            Span::dummy(),
        );
        self.temporaries.insert(id, label);
        let expr = self.syntax_arena.alloc(ast::Expr::new(
            ast::ExprKind::Path(ast::Path::new(id, &[], Span::dummy(), AstId::ZERO)),
            Span::dummy(),
            AstId::ZERO,
        ));
        (expr, label)
    }

    fn new_label(&mut self, ast_id: AstId) -> Label {
        let res = self.resolution[ast_id];
        let label = self.next_label();
        log::trace!("{label}: {res}");
        self.res_to_label.insert(res.res_id(), label);
        self.label_to_res.insert(label, res.res_id());
        label
    }

    pub fn get_label(&self, path: ast::Path<'ast>) -> Label {
        if path.ast_id == AstId::ZERO {
            let id = path.as_ident().unwrap();
            return self.temporaries[&id.ident];
        }
        let res = self.resolution[path.ast_id];
        log::trace!("get_label {res}");
        self.res_to_label[&res.res_id()]
    }

    pub fn get_label_type(&self, label: Label) -> Ty<'t> {
        self.label_to_type.get(&label).copied().unwrap()
    }

    fn push_item(&mut self, label: Label, body: mir::Expr) {
        let mir_id = self.module.items.push(mir::Item { label, body });
        self.module.label_to_mir_id.insert(label, mir_id);
    }

    fn lower(mut self) -> mir::Module {
        for (&res_id, _constructor) in &self.resolution.constructors {
            let label = self.next_label();
            self.res_to_label.insert(res_id, label);
            self.label_to_res.insert(label, res_id);
        }
        self.lower_comp_unit(self.program.unit);
        let main = self.lower_expr(self.program.main);
        self.push_item(MAIN_LABEL, main);
        self.module
    }

    fn lower_comp_unit(&mut self, unit: &'ast ast::CompUnit<'ast>) {
        self.lower_items(unit.items);
    }

    fn lower_mod_expr(&mut self, mexpr: &'ast Sp<ast::ModExpr<'ast>>) {
        match mexpr.value {
            ast::ModExpr::Path(_) => (),
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
                    let label = self.new_label(id.ast_id);
                    let body = self.lower_expr(expr);
                    self.push_item(label, body);
                }
                Item::Mod(_, mexpr) => self.lower_mod_expr(mexpr),
            }
        }
    }

    // Recursively construct a sequence of lowered binds representing the original
    // bind `pat = expr`. Since we completely eliminate compound patterns, a
    // single higher-level bind can produce multiple lowered binds.
    fn lower_bind(
        &mut self,
        pat: &'ast ast::Pat<'ast>,
        expr: &'ast ast::Expr<'ast>,
    ) -> Vec<(Label, mir::Expr)> {
        match pat.kind {
            PatKind::Wild => {
                // TODO. unused label.
                vec![(self.next_label(), self.lower_expr(expr))]
            }
            PatKind::Var(id) => {
                let label = self.new_label(id.ast_id);
                vec![(label, self.lower_expr(expr))]
            }
            PatKind::Ann(p, _) => self.lower_bind(p, expr),
            PatKind::Lit(_) => unreachable!("literal in binding pattern"),
            PatKind::Tuple(ps) => {
                // TODO. special handling for (x1, ..., xn) = (e1, ..., en) ?
                let mut split = Vec::new();
                // Hoist bound expr if it is not a path or literal.
                let expr = match expr.kind {
                    ExprKind::Path(_) | ExprKind::Lit(_) => expr,
                    _ => {
                        let (temp, label) = self.insert_temp();
                        split.push((label, self.lower_expr(expr)));
                        temp
                    }
                };
                for (i, p) in ps.iter().enumerate() {
                    for (label, bound) in self.lower_bind(p, expr) {
                        let label2 = match bound {
                            mir::Expr::Value(Value::Label(l)) => l,
                            _ => {
                                let label = self.next_label();
                                split.push((label, bound));
                                label
                            }
                        };
                        split.push((label, mir::Expr::Proj(label2, i)));
                    }
                }
                split
            }
            PatKind::Constructor(..) => {
                // We could allow this when the pattern is irrefutable,
                // i.e., only one constructor for the ADT.
                todo!("implement irrefutable pattern destructuring")
            }
            PatKind::Or(_) => todo!("implement or patterns"),
        }
    }

    fn lower_lit(&self, lit: ast::Lit) -> mir::Lit {
        match lit {
            ast::Lit::Unit => mir::Lit::Unit,
            ast::Lit::Bool(b) => mir::Lit::Bool(b),
            ast::Lit::Int32(s) => {
                mir::Lit::Int32(i32::from_str_radix(&s.as_str().replace("_", ""), 10).unwrap())
            }
            ast::Lit::Str(s) => mir::Lit::Str(s),
        }
    }

    fn lower_expr_to_value(
        &mut self,
        expr: &'ast ast::Expr<'ast>,
        binds: &mut Vec<(Label, mir::Expr)>,
    ) -> mir::Value {
        match self.lower_expr(expr) {
            mir::Expr::Value(v) => v,
            expr => {
                let label = self.next_label();
                binds.push((label, expr));
                Value::Label(label)
            }
        }
    }

    fn wrap_binds_over<I>(&self, binds: I, body: mir::Expr) -> mir::Expr
    where
        I: IntoIterator<Item = (Label, mir::Expr)>,
        I::IntoIter: DoubleEndedIterator,
    {
        binds.into_iter().rev().fold(body, |acc, (label, expr)| {
            mir::Expr::Let(label, Box::new(expr), Box::new(acc))
        })
    }

    fn lower_expr(&mut self, expr: &'ast ast::Expr<'ast>) -> mir::Expr {
        use ast::ExprKind;
        match expr.kind {
            ExprKind::Path(p) | ExprKind::Constructor(p) => {
                mir::Expr::Value(Value::Label(self.get_label(p)))
            }
            ExprKind::Lit(l) => mir::Expr::Value(Value::Lit(self.lower_lit(l))),
            ExprKind::External(s) => mir::Expr::Value(Value::External(s.sym)),
            ExprKind::Tuple(es) => {
                let mut binds = Vec::new();
                let es: Vec<_> = es
                    .iter()
                    .map(|e| self.lower_expr_to_value(e, &mut binds))
                    .collect();
                self.wrap_binds_over(binds, mir::Expr::Tuple(es))
            }
            ExprKind::Vector(es) => {
                let mut binds = Vec::new();
                let es: Vec<_> = es
                    .iter()
                    .map(|e| self.lower_expr_to_value(e, &mut binds))
                    .collect();
                self.wrap_binds_over(binds, mir::Expr::Vector(es))
            }
            ExprKind::Lambda(lambda) => {
                // \p1 .. pn -> e ~>
                //   \l1 .. ln -> lower(let p1 = l1, .., pn = ln in e)
                let mut args = Vec::with_capacity(lambda.args.len());
                let mut binds = Vec::new();
                for &arg in lambda.args {
                    let label = match arg.kind {
                        PatKind::Wild => self.next_label(),
                        PatKind::Var(id) => self.new_label(id.ast_id),
                        PatKind::Lit(_) => unreachable!("literal in lambda pattern"),
                        PatKind::Or(_) => unreachable!("or pattern in lambda pattern"),
                        _ => {
                            let (temp, label) = self.insert_temp();
                            binds.push((arg, *temp));
                            label
                        }
                    };
                    args.push(label);
                }
                let body = self.syntax_arena.alloc(ast::Expr::new(
                    ast::ExprKind::Let(self.syntax_arena.alloc_from_iter(binds), lambda.body),
                    lambda.body.span,
                    AstId::ZERO,
                ));
                let body = self.lower_expr(body);
                mir::Expr::Lambda(args, Box::new(body))
            }
            ExprKind::Ann(e, _) => self.lower_expr(e),
            ExprKind::If(cond, e1, e2) => {
                let cond = self.lower_expr(cond);
                if let mir::Expr::Value(Value::Label(label)) = cond {
                    mir::Expr::If(
                        label,
                        Box::new(self.lower_expr(e1)),
                        Box::new(self.lower_expr(e2)),
                    )
                } else {
                    let label = self.next_label();
                    mir::Expr::Let(
                        label,
                        Box::new(cond),
                        Box::new(mir::Expr::If(
                            label,
                            Box::new(self.lower_expr(e1)),
                            Box::new(self.lower_expr(e2)),
                        )),
                    )
                }
            }
            ExprKind::Let(binds, body) => {
                let mut new_binds = Vec::new();
                for (p, e) in binds {
                    new_binds.extend(self.lower_bind(p, e));
                }
                let body = self.lower_expr(body);
                self.wrap_binds_over(new_binds, body)
            }
            ExprKind::Call(f, args) => {
                // Lower (f e1 ... en) to
                // let l1 = lower(e1) in ... let ln = lower(en) in (f l1 ... ln).
                // If lower(ei) is already a value, don't add a superfluous bind.
                let mut binds = Vec::new();
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.lower_expr_to_value(arg, &mut binds))
                    .collect();
                let f_label = match self.lower_expr(f) {
                    mir::Expr::Value(Value::Label(label)) => label,
                    expr => {
                        let label = self.next_label();
                        binds.push((label, expr));
                        label
                    }
                };
                let body = mir::Expr::Call(f_label, args);
                self.wrap_binds_over(binds, body)
            }
            ExprKind::Case(e, arms) => {
                let (label, tree) = self.match_compile(e, arms);
                mir::Expr::Case(label, tree)
            }
            ExprKind::Seq(e1, e2) => {
                // Lower e1; e2 to let _l = lower(e1) in lower(e2).
                // TODO. unused label.
                mir::Expr::Let(
                    self.next_label(),
                    Box::new(self.lower_expr(e1)),
                    Box::new(self.lower_expr(e2)),
                )
            }
        }
    }
}
