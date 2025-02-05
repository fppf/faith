use core::panic;

use base::{hash::Map, index::Idx};
use hir::{
    Arena, CaseArm, CompUnit, Expr, ExprArg, ExprKind, HirId, Lambda, ModExpr, ModExprKind, Pat,
    PatKind, Path, Program, Ty,
};
use infer::InferData;
use span::{Ident, Span, Sym};

use crate::{
    MAIN_LABEL, Module,
    mir::{self, Label},
};

pub fn lower<'hir>(
    arena: &'hir Arena<'hir>,
    infer_data: InferData<'hir>,
    program: &'hir Program<'hir>,
) -> mir::Module {
    LoweringContext::new(arena, program, infer_data).lower()
}

// TODO. clean up profanity of maps.
pub(crate) struct LoweringContext<'hir> {
    module: mir::Module,
    hir_id_to_label: Map<HirId, Label>,
    label_to_hir_id: Map<Label, HirId>,
    label_to_type: Map<Label, Ty<'hir>>,
    local_to_label: Map<Ident, Label>,
    label: Label,
    program: &'hir Program<'hir>,
    pub infer_data: InferData<'hir>,
    hir_id: HirId,
    hir_arena: &'hir Arena<'hir>,
}

impl<'hir> LoweringContext<'hir> {
    fn new(
        hir_arena: &'hir Arena<'hir>,
        program: &'hir Program<'hir>,
        infer_data: InferData<'hir>,
    ) -> Self {
        Self {
            module: Module::default(),
            hir_id_to_label: Map::default(),
            label_to_hir_id: Map::default(),
            label_to_type: Map::default(),
            local_to_label: Map::default(),
            label: MAIN_LABEL.plus(1),
            program,
            infer_data,
            hir_id: program.last_hir_id.plus(1),
            hir_arena,
        }
    }

    fn next_hir_id(&mut self) -> HirId {
        let next = self.hir_id;
        self.hir_id = self.hir_id + 1;
        next
    }

    fn next_label(&mut self) -> Label {
        let label = self.label;
        self.label = self.label + 1;
        label
    }

    fn insert_temp(&mut self, typ: Ty<'hir>) -> (Path<'hir>, Label) {
        let label = self.next_label();
        let id = Ident::new(
            Sym::intern(&format!("~tmp{}", label.index())),
            Span::dummy(),
        );
        let hir_id = self.next_hir_id();
        self.hir_id_to_label.insert(hir_id, label);
        self.label_to_hir_id.insert(label, hir_id);
        self.label_to_type.insert(label, typ);
        self.local_to_label.insert(id, label);
        let path = self
            .hir_arena
            .path(id, [], Span::dummy(), hir::Res::Local(hir_id));
        (path, label)
    }

    fn insert_hir_id(&mut self, hir_id: HirId) -> Label {
        let label = self.next_label();
        self.hir_id_to_label.insert(hir_id, label);
        self.label_to_hir_id.insert(label, hir_id);
        let typ = self
            .infer_data
            .hir_id_to_type
            .get(&hir_id)
            .unwrap_or_else(|| panic!("no type for {hir_id}"));
        self.label_to_type.insert(label, *typ);
        label
    }

    fn insert_path(&mut self, path: Path<'hir>) -> Label {
        let hir_id = path.res().hir_id();
        self.insert_hir_id(hir_id)
    }

    fn get_path_label_opt(&self, path: Path<'hir>) -> Option<Label> {
        let hir_id = path.res().hir_id();
        self.hir_id_to_label.get(&hir_id).copied()
    }

    fn get_path_label(&self, path: Path<'hir>) -> Label {
        self.get_path_label_opt(path)
            .unwrap_or_else(|| panic!("no label found for {path}"))
    }

    pub fn get_local_label(&self, ident: Ident) -> Label {
        self.local_to_label.get(&ident).copied().unwrap()
    }

    pub fn get_local_hir_id(&self, ident: Ident) -> HirId {
        self.label_to_hir_id
            .get(&self.get_local_label(ident))
            .copied()
            .unwrap()
    }

    pub fn get_label_type(&self, label: Label) -> Ty<'hir> {
        self.label_to_type.get(&label).copied().unwrap()
    }

    fn push_item(&mut self, label: Label, body: mir::Expr) {
        let mir_id = self.module.items.push(mir::Item { label, body });
        self.module.label_to_mir_id.insert(label, mir_id);
    }

    fn lower(mut self) -> mir::Module {
        self.lower_comp_unit(self.program.unit);
        let main = self.lower_expr(self.program.main);
        self.push_item(MAIN_LABEL, main);
        self.module
    }

    fn lower_comp_unit(&mut self, unit: &'hir CompUnit<'hir>) {
        self.lower_items(unit.items);
    }

    fn lower_mod_expr(&mut self, mexpr: &'hir ModExpr<'hir>) {
        match mexpr.kind {
            ModExprKind::Path(_) => (),
            ModExprKind::Import(source_id) => {
                let unit = self
                    .program
                    .imports
                    .get(&source_id)
                    .expect("invalid import produced by HIR lowering");
                self.lower_comp_unit(unit);
            }
            ModExprKind::Struct(items) => self.lower_items(items),
        }
    }

    fn lower_items(&mut self, items: &'hir hir::Items<'hir>) {
        for (_, mexpr) in &items.modules {
            self.lower_mod_expr(mexpr);
        }

        for (_, value) in &items.values {
            let label = self.insert_path(value.path);
            let body = self.lower_expr(value.expr);
            self.push_item(label, body);
        }
    }

    // Recursively construct a sequence of lowered binds representing the original
    // HIR bind `pat = expr`. Since we completely eliminate compound patterns, a
    // single HIR bind can produce multiple MIR binds.
    fn lower_bind(&mut self, pat: &'hir Pat<'hir>, expr: Expr<'hir>) -> Vec<(Label, mir::Expr)> {
        match pat.kind {
            PatKind::Wild => {
                // TODO. unused label.
                vec![(self.next_label(), self.lower_expr(expr))]
            }
            PatKind::Var(id, hir_id) => {
                let label = self.insert_hir_id(hir_id);
                self.local_to_label.insert(id, label);
                vec![(label, self.lower_expr(expr))]
            }
            PatKind::Ann(p, _) => self.lower_bind(p, expr),
            PatKind::Lit(_) => unreachable!("literal in binding pattern"),
            PatKind::Tuple(ps) => {
                let mut split = Vec::new();

                // Hoist bound expr if it is not a path or literal.
                let expr = match expr.kind() {
                    ExprKind::Path(_) | ExprKind::Lit(_) => expr,
                    _ => {
                        let (path, label) = self.insert_temp(todo!());
                        split.push((label, self.lower_expr(expr)));
                        self.hir_arena.expr(ExprKind::Path(path), path.span())
                    }
                };

                for (i, p) in ps.iter().enumerate() {
                    let mut binds = self.lower_bind(p, expr);
                    for (_, bound) in &mut binds {
                        *bound = mir::Expr::Proj(Box::new(bound.clone()), i);
                    }
                    split.extend(binds);
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

    pub fn preprocess_case(
        &mut self,
        scrutinee: Expr<'hir>,
        arms: &'hir [CaseArm<'hir>],
    ) -> (Label, Ident, &'hir [CaseArm<'hir>]) {
        // Hoist the scrutinee in order to eliminate variable-only patterns in case arms.
        // For example,
        //
        //   case f x {
        //         y => z
        //   }
        //
        // will become
        //
        //   let tmp = f x in
        //   case tmp {
        //         _ => let y = tmp in z
        //   }
        //
        // There is no need to hoist paths, since we can just replace them directly with labels.

        fn replace_variable_pattern<'a>(pat: &'a Pat<'a>) -> (Pat<'a>, Option<Pat<'a>>) {
            if let PatKind::Var(..) = pat.kind {
                (
                    Pat {
                        kind: PatKind::Wild,
                        span: pat.span,
                    },
                    Some(*pat),
                )
            } else {
                (*pat, None)
            }
        }

        fn hoist_scrutinee<'a>(
            ctx: &mut LoweringContext<'a>,
            scrutinee: Expr<'a>,
        ) -> (Label, Expr<'a>, Ident) {
            if let ExprKind::Path(path) = scrutinee.kind()
                && let Some(id) = path.as_ident()
                && let Some(label) = ctx.get_path_label_opt(*path)
            {
                return (label, scrutinee, id);
            }
            let typ = ctx
                .infer_data
                .expr_types
                .get(&scrutinee)
                .unwrap_or_else(|| panic!("no type for {scrutinee}"));
            let (path, label) = ctx.insert_temp(*typ);
            let hoisted_scrutinee = ctx.hir_arena.expr(ExprKind::Path(path), path.span());
            (label, hoisted_scrutinee, path.id())
        }

        let (label, hoisted_scrutinee, id) = hoist_scrutinee(self, scrutinee);
        let mut new_arms = Vec::with_capacity(arms.len());
        for (pat, body) in arms {
            let (pat, bind) = replace_variable_pattern(pat);
            if let Some(bind) = bind {
                let body = self.hir_arena.expr(
                    ExprKind::Let(
                        self.hir_arena.alloc_from_iter([(bind, hoisted_scrutinee)]),
                        *body,
                    ),
                    body.span(),
                );
                new_arms.push((pat, body));
            } else {
                new_arms.push((pat, *body));
            }
        }
        (label, id, self.hir_arena.alloc_from_iter(new_arms))
    }

    fn lower_expr(&mut self, expr: Expr<'hir>) -> mir::Expr {
        match *expr.kind() {
            ExprKind::Path(p) | ExprKind::Constructor(p) => {
                mir::Expr::Label(self.get_path_label(p))
            }
            ExprKind::External(s, _) => mir::Expr::External(s),
            ExprKind::Lit(l) => mir::Expr::Lit(l),
            ExprKind::Tuple(es) => {
                mir::Expr::Tuple(es.iter().map(|&e| self.lower_expr(e)).collect())
            }
            ExprKind::Vector(es) => {
                mir::Expr::Vector(es.iter().map(|&e| self.lower_expr(e)).collect())
            }
            ExprKind::Lambda(lambda) => self.lower_lambda(lambda),
            ExprKind::Ann(e, _) => self.lower_expr(e),
            ExprKind::If(cond, e1, e2) => mir::Expr::If(
                Box::new(self.lower_expr(cond)),
                Box::new(self.lower_expr(e1)),
                Box::new(self.lower_expr(e2)),
            ),
            ExprKind::Let(binds, body) => {
                let mut new_binds = Vec::new();
                for (p, e) in binds {
                    new_binds.extend(self.lower_bind(p, *e));
                }
                let body = self.lower_expr(body);
                new_binds.into_iter().rev().fold(body, |acc, bind| {
                    mir::Expr::Let(bind.0, Box::new(bind.1), Box::new(acc))
                })
            }
            ExprKind::App(_u, e, args) => {
                // Lower (f e1 ... en) to
                // let l1 = lower(e1) in ... let ln = lower(en) in (f l1 ... ln).
                // If lower(ei) is already a label or literal, don't add a superfluous bind.
                let mut args: Vec<_> = args
                    .iter()
                    .flat_map(|arg| self.lower_expr_arg(arg))
                    .collect();
                let mut binds = Vec::new();
                for arg in &mut args {
                    match arg {
                        mir::Expr::Label(_) | mir::Expr::Lit(_) => (),
                        _ => {
                            let label = self.next_label();
                            binds.push((label, arg.clone()));
                            *arg = mir::Expr::Label(label);
                        }
                    };
                }
                let body = mir::Expr::App(Box::new(self.lower_expr(e)), args);
                binds.into_iter().rev().fold(body, |acc, bind| {
                    mir::Expr::Let(bind.0, Box::new(bind.1), Box::new(acc))
                })
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

    fn lower_expr_arg(&mut self, arg: &'hir ExprArg<'hir>) -> Option<mir::Expr> {
        match *arg {
            ExprArg::Expr(e) => Some(self.lower_expr(e)),
            ExprArg::Type(_) => None,
        }
    }

    fn lower_lambda(&mut self, lambda: Lambda<'hir>) -> mir::Expr {
        //
        // \p1 .. pn -> e ~>
        //   \l1 .. ln -> lower(let p1 = l1, .., pn = ln in e)
        //
        let mut args = Vec::with_capacity(lambda.args.len());
        let mut binds = Vec::new();
        for &arg in lambda.args {
            let label = match arg.kind {
                PatKind::Wild => self.next_label(),
                PatKind::Var(id, hir_id) => {
                    let label = self.insert_hir_id(hir_id);
                    self.local_to_label.insert(id, label);
                    label
                }
                PatKind::Lit(_) => unreachable!("literal in lambda pattern"),
                _ => {
                    let (path, label) = self.insert_temp(todo!());
                    let expr = self.hir_arena.expr(ExprKind::Path(path), Span::dummy());
                    binds.push((arg, expr));
                    label
                }
            };
            args.push(label);
        }
        let body = self.hir_arena.expr(
            ExprKind::Let(&*self.hir_arena.alloc_from_iter(binds), lambda.body),
            lambda.body.span(),
        );
        let body = self.lower_expr(body);
        mir::Expr::Lambda(args, Box::new(body))
    }
}
