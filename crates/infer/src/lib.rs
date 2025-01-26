#![feature(never_type)]
#![allow(unused)]

use base::{hash::Map, pp::FormatIterator};
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

#[derive(Default, Debug)]
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

    fn fresh(&mut self) -> Ident {
        let ch = (b'a' + self.char_count) as char;
        self.char_count = (self.char_count + 1) % (b'z' - b'a');
        let id = Ident::new(Sym::intern(&format!("'{ch}")), Span::dummy());
        self.stamp += 1;
        id
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
        let _unit_mtyp = self.infer_comp_unit(self.program.unit)?;
        let main_typ = self.infer_solve_expr(self.program.main)?;
        log::trace!("main : {main_typ}");
        self.zonk();
        Ok(self.infer_data)
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
                todo!()
                // if let Some(mtyp) = self.env.comp_units.get(&source_id) {
                //     return Ok(*mtyp);
                // } else {
                //     let comp_unit = self
                //         .program
                //         .imports
                //         .get(&source_id)
                //         .expect("HIR lowering produced an invalid source_id for an import");
                //     return self.infer_comp_unit(comp_unit);
                // }
            }
            ModExprKind::Path(path) => {
                todo!()
            }
            ModExprKind::Struct(items) => {
                log::trace!("{{");
                log::block_in();
                for (&id, value) in &items.values {
                    let typ = match value.typ {
                        Some(typ) => {
                            self.check_expr_poly(value.expr, typ)?;
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
                //log::trace!("{:?}", specs);
                Ok(())
            }
        }
    }

    fn infer_decl_group(&mut self, group: TypeDeclGroup<'hir>) -> Result<(), InferError<'hir>> {
        log::trace!("infer_decl_group");

        Ok(())
    }

    fn infer_item(&mut self) -> Result<(), InferError<'hir>> {
        Ok(())
    }

    fn type_from_lit(&self, lit: hir::Lit, span: Span) -> Ty<'hir> {
        let base = match lit {
            hir::Lit::Unit => BaseType::Unit,
            hir::Lit::Bool(_) => BaseType::Bool,
            hir::Lit::Str(_) => BaseType::Str,
            hir::Lit::Int32(_) => BaseType::Int32,
        };
        self.arena.typ(TyKind::Base(base), span)
    }

    fn constrain(&mut self, lhs: Ty<'hir>, rhs: Ty<'hir>) {
        log::trace!("constrain {lhs} ~ {rhs}");
        self.constraints.push(Constraint::equal(lhs, rhs));
    }

    fn fresh_var(&self) -> Ty<'hir> {
        self.subs.new_var().1
    }

    /// Generalize a type over its unification variables.
    ///
    /// For example, `generalize('1 -> '1) = 'a -> 'a`.
    fn generalize(&mut self, typ: Ty<'hir>) -> Ty<'hir> {
        log::trace!("generalize {typ}");
        self.type_var_src.reset();
        let typ = self.subs.apply(typ);
        let free_vars = typ.uni_vars();
        if !free_vars.is_empty() {
            for var in free_vars {
                self.subs.insert(
                    var.id,
                    Ty::type_var(self.arena, TypeVar::new(self.type_var_src.fresh())),
                );
            }
            self.subs.apply(typ)
        } else {
            typ
        }
    }

    fn instantiate(&mut self, typ: Ty<'hir>) -> Ty<'hir> {
        log::trace!("instantiate {typ}");
        let subs = typ
            .type_vars()
            .iter()
            .map(|&var| (var.name, self.fresh_var()))
            .collect();
        typ.subst_type_var(self.arena, &subs)
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

        SkolemReplacer {
            arena: self.arena,
            skolems,
        }
        .fold(typ)
    }

    /// Split a an application into (head, args). Can only be called on things which
    /// "look like applications", see note in `infer_app`.
    fn split_app(&self, expr: Expr<'hir>) -> (Expr<'hir>, &'hir [ExprArg<'hir>]) {
        match *expr.kind() {
            ExprKind::Path(_) | ExprKind::Constructor(_) => (expr, &[]),
            ExprKind::App(_, h, args) => (h, args),
            _ => unreachable!(),
        }
    }

    /// Check a pattern against a type.
    fn check_pat(
        &mut self,
        pat: &'hir Pat<'hir>,
        expected: Ty<'hir>,
    ) -> Result<(), InferError<'hir>> {
        log::block!(
            "check_pat {pat} :: {expected}",
            match (pat.kind, expected.kind()) {
                (PatKind::Wild, _) => Ok(()),
                (PatKind::Var(_, hir_id), _) => {
                    self.env.insert(hir_id, expected);
                    Ok(())
                }
                (PatKind::Lit(l), _) if self.type_from_lit(l, pat.span) == expected => Ok(()),
                (PatKind::Tuple(ps), TyKind::Tuple(ts)) => {
                    if ps.len() == ts.len() {
                        for (p, &t) in ps.iter().zip(*ts) {
                            self.check_pat(p, t)?;
                        }
                        Ok(())
                    } else {
                        Err(InferError::PatTupleLength(pat.span, ps.len(), ts.len()))
                    }
                }
                (_, _) => {
                    let typ = self.infer_pat(pat)?;
                    self.constrain(typ, expected);
                    Ok(())
                }
            }
        )
    }

    fn infer_pats(&mut self, pats: &'hir [Pat<'hir>]) -> Result<Vec<Ty<'hir>>, InferError<'hir>> {
        let mut typs = Vec::with_capacity(pats.len());
        for pat in pats {
            typs.push(self.infer_pat(pat)?);
        }
        Ok(typs)
    }

    /// Infer a type for a pattern.
    fn infer_pat(&mut self, pat: &'hir Pat<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        log::block!("infer_pat {pat}", match pat.kind {
            PatKind::Wild => Ok(self.fresh_var()),
            PatKind::Var(_, hir_id) => {
                let var = self.fresh_var();
                self.env.insert(hir_id, var);
                Ok(var)
            }
            PatKind::Lit(l) => Ok(self.type_from_lit(l, pat.span)),
            PatKind::Ann(pat, typ) => {
                self.check_pat(pat, *typ)?;
                Ok(*typ)
            }
            PatKind::Tuple(pats) => {
                Ok(Ty::tuple(self.arena, self.infer_pats(pats)?, pat.span))
            }
            PatKind::Constructor(cons, args) => {
                // TODO. well-formed check for cons_t
                let cons_typ = todo!(); //self.lookup_type(self.arena.path(cons, []))?;

                let cons_typ = self.instantiate(cons_typ);
                if args.is_empty() {
                    Ok(cons_typ)
                } else {
                    let arg_typs = self.infer_pats(args)?;
                    let ret_typ = self.fresh_var();

                    self.constrain(Ty::n_arrow(self.arena, arg_typs, ret_typ), cons_typ);
                    Ok(ret_typ)
                }
            }
            PatKind::Or(_pats) => todo!("implement or patterns"),
        })
    }

    /// Check an expression against a type.
    fn check_expr(&mut self, expr: Expr<'hir>, expected: Ty<'hir>) -> Result<(), InferError<'hir>> {
        match (*expr.kind(), expected.kind()) {
            (ExprKind::App(..) | ExprKind::Path(_), _) => self.check_app(expr, expected),
            (ExprKind::Lit(l), bt @ TyKind::Base(_))
                if self.type_from_lit(l, expr.span()).kind() == bt =>
            {
                Ok(())
            }
            (ExprKind::Lit(l), TyKind::Var(_)) => {
                self.constrain(expected, self.type_from_lit(l, expr.span()));
                Ok(())
            }
            (ExprKind::Lambda(lambda), TyKind::Var(_)) => {
                self.check_lambda_var(lambda.args, lambda.body, expected)
            }
            (ExprKind::Lambda(lambda), TyKind::Arrow(..)) => {
                self.check_lambda_arrow(lambda.args, lambda.body, expected)
            }
            (ExprKind::Tuple(es), TyKind::Tuple(ts)) => {
                if es.len() == ts.len() {
                    for (&e, &t) in es.iter().zip(*ts) {
                        self.check_expr(e, t)?;
                    }
                    Ok(())
                } else {
                    Err(InferError::ExprTupleLength(expr.span(), es.len(), ts.len()))
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
                Ok(())
            }
            (_, _) => {
                let typ = self.infer_expr(expr)?;
                self.constrain(typ, expected);
                Ok(())
            }
        }
    }

    /// Check an expression against a possibly-polymorphic type.
    fn check_expr_poly(
        &mut self,
        expr: Expr<'hir>,
        expected: Ty<'hir>,
    ) -> Result<(), InferError<'hir>> {
        let expected = self.skolemize(expected);
        self.check_expr(expr, expected)
    }

    /// Check an application expression against a type. Refer to note in `infer_app` about what
    /// qualifies as an application.
    fn check_app(&mut self, expr: Expr<'hir>, expected: Ty<'hir>) -> Result<(), InferError<'hir>> {
        log::block!("check_app {expr} :: {expected}", {
            let (head, args) = self.split_app(expr);
            let head_typ = self.infer_app_head(head)?;
            let head_typ = self.instantiate(head_typ);

            let mut typ = head_typ;
            for arg in args {
                if let TyKind::Arrow(_, arg_typ, ret_typ) = *typ.kind() {
                    self.check_expr_arg(*arg, arg_typ)?;
                    typ = ret_typ;
                } else {
                    break;
                }
            }

            self.constrain(typ, expected);
            Ok(())
        })
    }

    fn check_expr_arg(
        &mut self,
        arg: ExprArg<'hir>,
        expected: Ty<'hir>,
    ) -> Result<(), InferError<'hir>> {
        match arg {
            ExprArg::Expr(e) => self.check_expr(e, expected),
            ExprArg::Type(_t) => todo!("VTA"),
        }
    }

    /// Check a lambda expression `(\args -> body)` against a unification variable.
    fn check_lambda_var(
        &mut self,
        args: &'hir [Pat<'hir>],
        body: Expr<'hir>,
        var: Ty<'hir>,
    ) -> Result<(), InferError<'hir>> {
        let mut arg_typs = Vec::with_capacity(args.len());
        let ret_typ = self.check_lambda_var_inner(args, body, var, &mut arg_typs)?;
        self.constrain(var, Ty::n_arrow(self.arena, arg_typs, ret_typ));
        Ok(())
    }

    // Helper for `check_lambda_var`.
    fn check_lambda_var_inner(
        &mut self,
        args: &'hir [Pat<'hir>],
        body: Expr<'hir>,
        var: Ty<'hir>,
        arg_typs: &mut Vec<Ty<'hir>>,
    ) -> Result<Ty<'hir>, InferError<'hir>> {
        if let Some((first, rest)) = args.split_first() {
            let typ = self.infer_pat(first)?;
            arg_typs.push(typ);
            self.check_lambda_var_inner(rest, body, typ, arg_typs)
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
            self.check_expr_poly(body, arrow)
        }
    }

    /// Infer a type for an expression.
    fn infer_expr(&mut self, expr: Expr<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        let res = match *expr.kind() {
            ExprKind::App(..) | ExprKind::Path(_) | ExprKind::Constructor(_) => {
                self.infer_app(expr)?
            }
            ExprKind::External(_s) => todo!(),
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
                self.check_expr(expr, *typ)?;
                *typ
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

    /// Infer the type of an application.
    ///
    /// NB. Here, an application can be either a function call (such as `(f a b ...)`) or simply
    /// a "0-arity" application, like a variable or path.
    fn infer_app(&mut self, expr: Expr<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        log::block!("infer_app {expr}", {
            let (head, args) = self.split_app(expr);
            let head_typ = self.infer_app_head(head)?;
            let head_typ = self.instantiate(head_typ);

            let mut typ = head_typ;
            for arg in args {
                if let TyKind::Arrow(_, arg_typ, ret_typ) = *typ.kind() {
                    self.check_expr_arg(*arg, arg_typ)?;
                    typ = ret_typ;
                } else {
                    break;
                }
            }
            Ok(typ)
        })
    }

    /// Infer the head of an application; really just a wrapper around `infer_expr`.
    fn infer_app_head(&mut self, expr: Expr<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        match *expr.kind() {
            ExprKind::Path(p) | ExprKind::Constructor(p) => self.infer_path(p),
            _ => self.infer_expr(expr),
        }
    }

    /// Infer the type of a path by looking it up in the environment.
    fn infer_path(&mut self, path: Path<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        let hir_id = path.res().hir_id();
        match self.env.get(&hir_id) {
            Some(typ) => Ok(*typ),
            None => {
                let value = self.program.values.get(&hir_id).unwrap();
                let typ = match value.typ {
                    Some(typ) => {
                        self.check_expr_poly(value.expr, typ)?;
                        typ
                    }
                    None => self.infer_expr(value.expr)?,
                };
                self.env.insert(hir_id, typ);
                Ok(typ)
            }
        }
    }

    fn solve_current(&mut self) -> Result<(), InferError<'hir>> {
        log::block!("solve_current", {
            let constraints: Vec<_> = self.constraints.drain(..).collect();
            let residual =
                constraint::solve(self, constraints).map_err(InferError::TypeUnifyFail)?;
            if residual.is_empty() {
                Ok(())
            } else {
                log::trace!("residual: {}", residual.iter().format(", "));
                Err(InferError::ResidualConstraints(residual))
            }
        })
    }

    fn infer_solve_expr(&mut self, expr: Expr<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        let res = self.infer_expr(expr)?;
        self.solve_current()?;
        let res = self.generalize(res);
        self.infer_data.expr_types.insert(expr, res);
        Ok(res)
    }

    fn zonk(&mut self) {
        for (_, t) in self.infer_data.expr_types.iter_mut() {
            *t = self.subs.apply(*t);
        }
    }
}
