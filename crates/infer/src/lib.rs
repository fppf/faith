#![feature(never_type)]
#![feature(let_chains)]

use base::hash::Map;
use hir::*;
use span::{Ident, Span, Sym, diag::Diagnostic};

mod constraint;
mod substitution;
mod unify;

pub mod error;

use constraint::Constraint;
use error::InferError;
use substitution::Substitution;
use unify::{UnificationTable, UnifyKey};

pub fn infer_program_in<'hir>(
    arena: &'hir Arena<'hir>,
    program: &'hir Program<'hir>,
) -> Result<InferData<'hir>, Diagnostic> {
    TypeChecker::new(arena, program)
        .infer()
        .map_err(Diagnostic::from)
}

#[derive(Default)]
pub struct InferData<'hir> {
    pub expr_types: Map<Expr<'hir>, Ty<'hir>>,
    pub adts: Map<Ident, Ty<'hir>>,
    pub ctor_to_adt: Map<Ident, (usize /* arity */, Ty<'hir> /* variant type */)>,
}

struct TypeChecker<'hir> {
    arena: &'hir Arena<'hir>,
    program: &'hir Program<'hir>,
    env: HirMap<Ty<'hir>>,
    type_var_src: TypeVarSource,
    skolem: SkolemId,
    constraints: Vec<Constraint<'hir, Ty<'hir>>>,
    subs: Substitution<'hir, Ty<'hir>>,
    webs: UnificationTable<WebId>,
    infer_data: InferData<'hir>,
}

impl UnifyKey for WebId {
    type Value = ();
}

struct TypeVarSource {
    stamp: u32,
    char_count: u8,
}

impl TypeVarSource {
    fn new(stamp: u32) -> Self {
        Self {
            stamp,
            char_count: 0,
        }
    }

    fn reset(&mut self) {
        self.char_count = 0;
    }

    fn fresh(&mut self) -> TypeVar {
        let ch = (b'a' + self.char_count) as char;
        self.char_count = (self.char_count + 1) % (b'z' - b'a');
        let id = Ident::new(Sym::intern(&format!("'{ch}")), Span::dummy());
        self.stamp += 1;
        TypeVar::new(id)
    }
}

/// Split an application into (head, args). Can only be called on things which
/// "look like applications", see note in `infer_app`.
fn split_app(expr: Expr<'_>) -> (Expr<'_>, &[ExprArg<'_>]) {
    match *expr.kind() {
        ExprKind::Path(_) | ExprKind::Constructor(..) => (expr, &[]),
        ExprKind::App(_, h, args) => (h, args),
        _ => unreachable!(),
    }
}

impl<'hir> TypeChecker<'hir> {
    fn new(arena: &'hir Arena<'hir>, program: &'hir Program<'hir>) -> Self {
        Self {
            arena,
            program,
            env: HirMap::default(),
            type_var_src: TypeVarSource::new(1),
            skolem: SkolemId::ZERO,
            constraints: Vec::new(),
            subs: Substitution::new(arena),
            webs: UnificationTable::default(),
            infer_data: InferData::default(),
        }
    }

    fn infer(mut self) -> Result<InferData<'hir>, InferError<'hir>> {
        self.infer_comp_unit(self.program.unit)?;
        let main_typ = self.infer_solve_expr(self.program.main)?;
        log::trace!("main : {main_typ}");
        for (_, t) in self.infer_data.expr_types.iter_mut() {
            *t = self.subs.apply(*t);
        }
        Ok(self.infer_data)
    }

    fn type_from_lit(&self, lit: hir::Lit, span: Span) -> Ty<'hir> {
        self.arena.typ(TyKind::Base(lit.base_type()), span)
    }

    fn constrain(&mut self, lhs: Ty<'hir>, rhs: Ty<'hir>) {
        log::trace!("{lhs} ~ {rhs}");
        self.constraints.push(Constraint::equal(lhs, rhs));
    }

    fn fresh_var(&self) -> Ty<'hir> {
        self.subs.new_var().1
    }

    /// Generalize a type over its unification variables.
    ///
    /// For example, `generalize('1 -> '1) = 'a -> 'a`.
    fn generalize(&mut self, typ: Ty<'hir>) -> Ty<'hir> {
        self.type_var_src.reset();
        let typ = self.subs.apply(typ);
        let free_vars = typ.uni_vars();
        if !free_vars.is_empty() {
            for var in free_vars {
                self.subs
                    .insert(var.id, Ty::type_var(self.arena, self.type_var_src.fresh()));
            }
            self.subs.apply(typ)
        } else {
            typ
        }
    }

    fn instantiate(&mut self, typ: Ty<'hir>) -> Ty<'hir> {
        struct Instantiator<'a> {
            arena: &'a Arena<'a>,
            subs: Map<Ident, Ty<'a>>,
        }

        impl<'a> Folder<'a, Ty<'a>> for Instantiator<'a> {
            fn arena(&self) -> &'a Arena<'a> {
                self.arena
            }

            fn fold(&mut self, typ: Ty<'a>) -> Ty<'a> {
                if let TyKind::Var(var) = typ.kind()
                    && let Some(&other) = self.subs.get(&var.name)
                {
                    other
                } else {
                    typ.fold_with(self)
                }
            }
        }

        Instantiator {
            arena: self.arena,
            subs: typ
                .type_vars()
                .iter()
                .map(|&var| (var.name, self.fresh_var()))
                .collect(),
        }
        .fold(typ)
    }

    fn fresh_skolem(&mut self) -> SkolemId {
        let id = self.skolem;
        self.skolem = self.skolem + 1;
        id
    }

    fn skolemize(&mut self, typ: Ty<'hir>) -> Ty<'hir> {
        struct SkolemReplacer<'a> {
            skolems: Map<TypeVar, Skolem>,
            arena: &'a Arena<'a>,
        }

        impl<'a> Folder<'a, Ty<'a>> for SkolemReplacer<'a> {
            fn arena(&self) -> &'a Arena<'a> {
                self.arena
            }

            fn fold(&mut self, typ: Ty<'a>) -> Ty<'a> {
                if let TyKind::Var(var) = typ.kind() {
                    Ty::skolem(self.arena, self.skolems[var])
                } else {
                    typ.fold_with(self)
                }
            }
        }

        let skolems = typ
            .type_vars()
            .iter()
            .map(|&var| (var, Skolem::new(self.fresh_skolem(), var.name)))
            .collect();

        let skolemized = SkolemReplacer {
            arena: self.arena,
            skolems,
        }
        .fold(typ);
        if typ != skolemized {
            log::trace!("skolemize ({typ}) => ({skolemized})");
        }
        skolemized
    }

    fn solve_current(&mut self) -> Result<(), InferError<'hir>> {
        let constraints: Vec<_> = self.constraints.drain(..).collect();
        let residual = constraint::solve(self, constraints).map_err(InferError::TypeUnifyFail)?;
        if residual.is_empty() {
            Ok(())
        } else {
            Err(InferError::ResidualConstraints(residual))
        }
    }

    fn infer_solve_expr(&mut self, expr: Expr<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        let res = self.infer_expr(expr)?;
        self.solve_current()?;
        let res = self.generalize(res);
        self.infer_data.expr_types.insert(expr, res);
        Ok(res)
    }

    fn infer_comp_unit(&mut self, unit: &'hir CompUnit<'hir>) -> Result<(), InferError<'hir>> {
        let mexpr = self.arena.alloc(ModExpr {
            kind: ModExprKind::Struct(unit.items),
            span: Span::dummy(),
        });
        self.infer_mod_expr(mexpr)
    }

    fn infer_mod_expr(&mut self, mexpr: &'hir ModExpr<'hir>) -> Result<(), InferError<'hir>> {
        match mexpr.kind {
            ModExprKind::Import(source_id) => {
                let comp_unit = self
                    .program
                    .imports
                    .get(&source_id)
                    .expect("HIR lowering produced an invalid source_id for an import");
                self.infer_comp_unit(comp_unit)
            }
            ModExprKind::Path(_path) => {
                todo!()
            }
            ModExprKind::Struct(items) => {
                log::trace!("{{");
                log::block_in();
                for (&id, value) in &items.values {
                    let typ = match value.typ {
                        Some(typ) => {
                            self.check_expr(value.expr, typ)?;
                            self.solve_current()?;
                            typ
                        }
                        None => self.infer_solve_expr(value.expr)?,
                    };
                    log::trace!("{id} : {typ}");
                }
                for (id, mexpr) in &items.modules {
                    log::trace!("mod {id}");
                    self.infer_mod_expr(mexpr)?;
                }
                log::block_out();
                log::trace!("}}");
                Ok(())
            }
        }
    }

    fn _infer_decl_group(&mut self, _group: TypeDeclGroup<'hir>) -> Result<(), InferError<'hir>> {
        todo!()
    }

    /// Infer a type for an expression.
    fn infer_expr(&mut self, expr: Expr<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        let res = match *expr.kind() {
            // NB. Applications are either function calls (such as `(f a b ...)`)
            //     or "0-arity" applications, i.e., paths.
            ExprKind::App(..) | ExprKind::Path(_) | ExprKind::Constructor(..) => {
                let (head, args) = split_app(expr);
                let head_typ = match *head.kind() {
                    ExprKind::Path(p) | ExprKind::Constructor(p) => self.infer_path(p),
                    _ => self.infer_expr(head),
                }?;
                let mut typ = self.instantiate(head_typ);
                for arg in args {
                    if let TyKind::Arrow(_, arg_typ, ret_typ) = *typ.kind() {
                        match *arg {
                            ExprArg::Expr(e) => self.check_expr(e, arg_typ)?,
                            ExprArg::Type(_t) => todo!("VTA"),
                        }
                        typ = ret_typ;
                    } else {
                        break;
                    }
                }
                typ
            }
            ExprKind::External(_, typ) => typ,
            ExprKind::Lit(l) => self.type_from_lit(l, expr.span()),
            ExprKind::Lambda(lambda) => self.infer_lambda(lambda.args, lambda.body)?,
            ExprKind::Let(binds, body) => {
                for bind in binds {
                    let pat_typ = self.infer_pat(&bind.0)?;
                    let bind_typ = self.infer_expr(bind.1)?;
                    self.constrain(pat_typ, bind_typ);
                }
                self.infer_expr(body)?
            }
            ExprKind::Ann(expr, typ) => {
                self.check_expr(expr, typ)?;
                typ
            }
            ExprKind::Tuple(elems) => {
                let mut typs = Vec::with_capacity(elems.len());
                for &elem in elems {
                    typs.push(self.infer_expr(elem)?);
                }
                Ty::tuple(self.arena, typs, expr.span())
            }
            ExprKind::Vector(elems) => {
                let base_typ = self.fresh_var();
                if !elems.is_empty() {
                    for &elem in elems {
                        let elem_typ = self.infer_expr(elem)?;
                        self.constrain(base_typ, elem_typ);
                    }
                }
                self.arena.typ(TyKind::Vector(base_typ), expr.span())
            }
            ExprKind::Seq(e1, e2) => {
                self.check_expr(
                    e1,
                    self.arena.typ(TyKind::Base(BaseType::Unit), Span::dummy()),
                )?;
                self.infer_expr(e2)?
            }
            ExprKind::Case(scrutinee, arms) => {
                let typ = self.infer_expr(scrutinee)?;
                let var = self.fresh_var();
                for arm in arms {
                    let pat_typ = self.infer_pat(&arm.0)?;
                    self.constrain(typ, pat_typ);
                    let arm_typ = self.infer_expr(arm.1)?;
                    self.constrain(var, arm_typ);
                }
                var
            }
            ExprKind::If(cond, then_expr, else_expr) => {
                self.check_expr(
                    cond,
                    self.arena.typ(TyKind::Base(BaseType::Bool), Span::dummy()),
                )?;
                let then_typ = self.infer_expr(then_expr)?;
                let else_typ = self.infer_expr(else_expr)?;
                self.constrain(then_typ, else_typ);
                then_typ
            }
        };
        self.infer_data.expr_types.insert(expr, res);
        Ok(res)
    }

    /// Infer the type of a lambda expression `(\args -> body)`.
    fn infer_lambda(
        &mut self,
        args: &'hir [Pat<'hir>],
        body: Expr<'hir>,
    ) -> Result<Ty<'hir>, InferError<'hir>> {
        if let Some((first, rest)) = args.split_first() {
            let arg_typ = self.infer_pat(first)?;
            let ret_typ = self.infer_lambda(rest, body)?;
            Ok(Ty::arrow(self.arena, NO_WEB, arg_typ, ret_typ))
        } else {
            self.infer_expr(body)
        }
    }

    /// Infer the type of a path by looking it up in the environment.
    fn infer_path(&mut self, path: Path<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        let hir_id = path.res().hir_id();
        match self.env.get(&hir_id) {
            Some(typ) => Ok(*typ),
            None => {
                let typ = if let Some(cons) = self.program.constructors.get(&hir_id) {
                    cons.typ
                } else {
                    let value = self
                        .program
                        .values
                        .get(&hir_id)
                        .unwrap_or_else(|| panic!("ICE: expected '{path}' to be lowered"));

                    if value.recursive {
                        let fn_var = self.fresh_var();
                        self.env.insert(hir_id, fn_var);
                        return Ok(fn_var);
                    }

                    match value.typ {
                        Some(typ) => {
                            self.check_expr(value.expr, typ)?;
                            typ
                        }
                        None => self.infer_expr(value.expr)?,
                    }
                };
                self.env.insert(hir_id, typ);
                Ok(typ)
            }
        }
    }

    /// Infer a type for a pattern.
    fn infer_pat(&mut self, pat: &'hir Pat<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        Ok(match pat.kind {
            PatKind::Wild => self.fresh_var(),
            PatKind::Var(_, hir_id) => {
                let var = self.fresh_var();
                self.env.insert(hir_id, var);
                var
            }
            PatKind::Lit(l) => self.type_from_lit(l, pat.span),
            PatKind::Ann(pat, typ) => {
                self.check_pat(pat, typ)?;
                typ
            }
            PatKind::Tuple(pats) => Ty::tuple(self.arena, self.infer_pats(pats)?, pat.span),
            PatKind::Constructor(cons, args) => {
                // TODO. well-formed check for cons_t
                let cons_typ = self.infer_path(cons)?;
                if args.is_empty() {
                    cons_typ
                } else {
                    let arg_typs = self.infer_pats(args)?;
                    let ret_typ = self.fresh_var();
                    let cons_typ = self.instantiate(cons_typ);
                    self.constrain(Ty::n_arrow(self.arena, arg_typs, ret_typ), cons_typ);
                    ret_typ
                }
            }
            PatKind::Or(_pats) => todo!("implement or patterns"),
        })
    }

    fn infer_pats(&mut self, pats: &'hir [Pat<'hir>]) -> Result<Vec<Ty<'hir>>, InferError<'hir>> {
        let mut typs = Vec::with_capacity(pats.len());
        for pat in pats {
            typs.push(self.infer_pat(pat)?);
        }
        Ok(typs)
    }

    /// Check an expression against a type.
    fn check_expr(&mut self, expr: Expr<'hir>, expected: Ty<'hir>) -> Result<(), InferError<'hir>> {
        //let expected = self.skolemize(expected);
        match (*expr.kind(), expected.kind()) {
            (ExprKind::Lit(l), TyKind::Base(b)) if l.base_type() == *b => (),
            (ExprKind::Lit(l), TyKind::Var(_)) => {
                self.constrain(expected, self.type_from_lit(l, expr.span()));
            }

            // TODO. these branches probably aren't necessary
            (ExprKind::Lambda(lambda), TyKind::Uni(_)) => {
                let mut arg_typs = Vec::with_capacity(lambda.args.len());
                let ret_typ =
                    self.check_lambda_var(lambda.args, lambda.body, expected, &mut arg_typs)?;
                self.constrain(expected, Ty::n_arrow(self.arena, arg_typs, ret_typ));
            }
            (ExprKind::Lambda(lambda), TyKind::Arrow(..)) => {
                self.check_lambda_arrow(lambda.args, lambda.body, expected)?
            }

            (ExprKind::Tuple(es), TyKind::Tuple(ts)) => {
                if es.len() == ts.len() {
                    for (&e, &t) in es.iter().zip(*ts) {
                        self.check_expr(e, t)?;
                    }
                } else {
                    return Err(InferError::ExprTupleLength(expr.span(), es.len(), ts.len()));
                }
            }
            (ExprKind::Case(scrutinee, arms), _) => {
                let typ = self.infer_expr(scrutinee)?;
                for arm in arms {
                    let pat_typ = self.infer_pat(&arm.0)?;
                    self.constrain(typ, pat_typ);
                    let arm_typ = self.infer_expr(arm.1)?;
                    self.constrain(arm_typ, expected);
                }
            }
            (_, _) => {
                let typ = self.infer_expr(expr)?;
                self.constrain(typ, expected);
            }
        }
        Ok(())
    }

    fn check_lambda_var(
        &mut self,
        args: &'hir [Pat<'hir>],
        body: Expr<'hir>,
        var: Ty<'hir>,
        arg_typs: &mut Vec<Ty<'hir>>,
    ) -> Result<Ty<'hir>, InferError<'hir>> {
        if let Some((first, rest)) = args.split_first() {
            let typ = self.infer_pat(first)?;
            arg_typs.push(typ);
            self.check_lambda_var(rest, body, typ, arg_typs)
        } else {
            self.check_expr(body, var)?;
            Ok(var)
        }
    }

    /// Check a lambda expression `(\args -> body)` against an arrow type.
    fn check_lambda_arrow(
        &mut self,
        args: &'hir [Pat<'hir>],
        body: Expr<'hir>,
        arrow: Ty<'hir>,
    ) -> Result<(), InferError<'hir>> {
        if let Some((first, rest)) = args.split_first() {
            match *arrow.kind() {
                TyKind::Arrow(_, arg, ret) => {
                    self.check_pat(first, arg)?;
                    self.check_lambda_arrow(rest, body, ret)
                }
                _ if rest.is_empty() => self.check_pat(first, arrow),
                _ => unreachable!(),
            }
        } else {
            self.check_expr(body, arrow)
        }
    }

    /// Check a pattern against a type.
    fn check_pat(
        &mut self,
        pat: &'hir Pat<'hir>,
        expected: Ty<'hir>,
    ) -> Result<(), InferError<'hir>> {
        match (pat.kind, expected.kind()) {
            (PatKind::Wild, _) => (),
            (PatKind::Var(_, hir_id), _) => {
                self.env.insert(hir_id, expected);
            }
            (PatKind::Lit(l), TyKind::Base(b)) if l.base_type() == *b => (),
            (PatKind::Tuple(ps), TyKind::Tuple(ts)) => {
                if ps.len() == ts.len() {
                    for (p, &t) in ps.iter().zip(*ts) {
                        self.check_pat(p, t)?;
                    }
                } else {
                    return Err(InferError::PatTupleLength(pat.span, ps.len(), ts.len()));
                }
            }
            (_, _) => {
                let typ = self.infer_pat(pat)?;
                self.constrain(typ, expected);
            }
        }
        Ok(())
    }
}
