use base::{hash::Map, index::Idx};
use hir::{
    Arena, CaseArm, CompUnit, Expr, ExprArg, ExprKind, HirId, Lambda, ModExpr, ModExprKind, Pat,
    PatKind, Path, Program,
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

pub(crate) struct LoweringContext<'hir> {
    module: mir::Module,
    hir_id_to_label: Map<HirId, Label>,
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
            label: Label::new(MAIN_LABEL.index() + 1),
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
        self.label = Label::new(self.label.index() + 1);
        label
    }

    pub fn insert_temp(&mut self) -> (Path<'hir>, Label) {
        let label = self.next_label();
        let id = Ident::new(
            Sym::intern(&format!("~tmp{}", label.index())),
            Span::dummy(),
        );
        let hir_id = self.next_hir_id();
        self.hir_id_to_label.insert(hir_id, label);
        let path = self
            .hir_arena
            .path(id, [], Span::dummy(), hir::Res::Local(hir_id));
        (path, label)
    }

    fn insert_hir_id(&mut self, hid_id: HirId) -> Label {
        let label = self.next_label();
        self.hir_id_to_label.insert(hid_id, label);
        label
    }

    fn get_id_label_opt(&self, hir_id: HirId) -> Option<Label> {
        self.hir_id_to_label.get(&hir_id).copied()
    }

    pub fn get_id_label(&self, hir_id: HirId) -> Label {
        self.get_id_label_opt(hir_id).unwrap()
    }

    fn insert_path(&mut self, path: Path<'hir>) -> Label {
        let hir_id = path.res().hir_id();
        self.insert_hir_id(hir_id)
    }

    fn get_path_label_opt(&self, path: Path<'hir>) -> Option<Label> {
        let hir_id = path.res().hir_id();
        self.get_id_label_opt(hir_id)
    }

    fn get_path_label(&self, path: Path<'hir>) -> Label {
        self.get_path_label_opt(path)
            .expect(&format!("No label found for {path}"))
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
        //for item in unit.items {
        //    self.lower_item(item);
        //}
    }

    fn lower_mod_expr(&mut self, mexpr: &'hir ModExpr<'hir>) {
        match mexpr.kind {
            ModExprKind::Path(_) | ModExprKind::Import(_) => (),
            ModExprKind::Struct(items) => {
                //for item in items {
                //    self.lower_item(item);
                //}
            }
        }
    }

    /*
    fn lower_item(&mut self, item: &'hir Item<'hir>) {
        match item.kind {
            ItemKind::Val(id, _, expr) => {
                let label = self.insert_id(id);
                let body = self.lower_expr(expr);
                self.push_item(label, body);
            }
            ItemKind::ValFn(id, _, lambda) => {
                let label = self.insert_id(id);
                let body = self.lower_lambda(lambda);
                self.push_item(label, body);
            }
            ItemKind::External(id, _, sym) => {
                let label = self.insert_id(id);
                self.push_item(label, mir::Expr::External(sym));
            }
            ItemKind::Type(group) => {
                for decl in group.decls {
                    if let TyKind::Variant(vs) = decl.kind.kind() {
                        for (id, _) in vs.iter() {
                            self.insert_id(*id);
                        }
                    }
                }
            }
            ItemKind::Mod(_, mexpr) => self.lower_mod_expr(mexpr),
            ItemKind::ModType(..) | ItemKind::Use(_) => (),
        }
    }
    */

    fn lower_bind(&mut self, pat: &'hir Pat<'hir>, expr: Expr<'hir>) -> Vec<(Label, mir::Expr)> {
        match pat.kind {
            PatKind::Wild => {
                vec![(self.next_label(), self.lower_expr(expr))]
            }
            PatKind::Var(_, hir_id) => {
                let label = self.insert_hir_id(hir_id);
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
                        let (path, label) = self.insert_temp();
                        split.push((label, self.lower_expr(expr)));
                        Expr::new(self.hir_arena, ExprKind::Path(path), Span::dummy())
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
            PatKind::Constructor(_, _) => {
                // We could allow this when the pattern is irrefutable,
                // i.e., only one constructor for the ADT.
                todo!()
            }
            _ => todo!(),
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
            if let ExprKind::Path(path) = scrutinee.kind() {
                if let Some(id) = path.as_ident() {
                    if let Some(label) = ctx.get_path_label_opt(*path) {
                        return (label, scrutinee, id);
                    }
                }
            }
            let (path, label) = ctx.insert_temp();
            let hoisted_scrutinee = ctx.hir_arena.expr(ExprKind::Path(path), path.span());
            (label, hoisted_scrutinee, path.id())
        }

        let (label, hoisted_scrutinee, id) = hoist_scrutinee(self, scrutinee);
        let mut new_arms = Vec::with_capacity(arms.len());
        for (pat, body) in arms {
            let (pat, bind) = replace_variable_pattern(pat);
            if let Some(bind) = bind {
                let body = Expr::new(
                    self.hir_arena,
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
            ExprKind::Seq(e1, e2) => mir::Expr::Let(
                self.next_label(),
                Box::new(self.lower_expr(e1)),
                Box::new(self.lower_expr(e2)),
            ),
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
                PatKind::Var(_, hir_id) => self.insert_hir_id(hir_id),
                PatKind::Lit(_) => unreachable!("literal in lambda pattern"),
                _ => {
                    let (path, label) = self.insert_temp();
                    let expr = self.hir_arena.expr(ExprKind::Path(path), Span::dummy());
                    binds.push((arg, expr));
                    label
                }
            };
            args.push(label);
        }
        let body = Expr::new(
            self.hir_arena,
            ExprKind::Let(&*self.hir_arena.alloc_from_iter(binds), lambda.body),
            lambda.body.span(),
        );
        let body = self.lower_expr(body);
        mir::Expr::Lambda(args, Box::new(body))
    }
}
