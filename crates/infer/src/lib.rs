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
    hir_ctxt: &'hir HirCtxt<'hir>,
    program: &'hir Program<'hir>,
) -> Result<(), Diagnostic> {
    TypeChecker::new(hir_ctxt, program)
        .infer()
        .map_err(Diagnostic::from)
}

struct TypeChecker<'hir> {
    hir_ctxt: &'hir HirCtxt<'hir>,
    program: &'hir Program<'hir>,
    type_var_src: TypeVarSource,
    skolem: SkolemId,
    constraints: Vec<Constraint<'hir, Ty<'hir>>>,
    subs: Substitution<'hir, Ty<'hir>>,
    webs: UnificationTable<WebId>,
}

impl UnifyKey for WebId {
    type Value = ();
}

#[derive(Default)]
struct TypeVarSource {
    char_count: u8,
}

impl TypeVarSource {
    fn reset(&mut self) {
        self.char_count = 0;
    }

    fn fresh(&mut self, _hir_id: HirId) -> TypeVar {
        let ch = (b'a' + self.char_count) as char;
        self.char_count = (self.char_count + 1) % (b'z' - b'a');
        let id = Ident::new(Sym::intern(&format!("'{ch}")), Span::dummy());
        TypeVar::new(id)
    }
}

impl<'hir> TypeChecker<'hir> {
    fn new(hir_ctxt: &'hir HirCtxt<'hir>, program: &'hir Program<'hir>) -> Self {
        Self {
            hir_ctxt,
            program,
            type_var_src: TypeVarSource::default(),
            skolem: SkolemId::ZERO,
            constraints: Vec::new(),
            subs: Substitution::new(hir_ctxt),
            webs: UnificationTable::default(),
        }
    }

    fn infer(mut self) -> Result<(), InferError<'hir>> {
        self.infer_comp_unit(self.program.unit)?;
        let main_typ = self.infer_solve_expr(self.program.main)?;
        log::trace!("main : {main_typ}");
        assert!(self.hir_ctxt.is_ctxt_typed());
        Ok(())
    }

    fn type_from_lit(&self, lit: hir::Lit, span: Span) -> Ty<'hir> {
        self.hir_ctxt.typ(TyKind::Base(lit.base_type()), span)
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
                self.subs.insert(
                    var.id,
                    Ty::type_var(self.hir_ctxt, self.type_var_src.fresh(HirId::ZERO)),
                );
            }
            self.subs.apply(typ)
        } else {
            typ
        }
    }

    fn instantiate(&mut self, typ: Ty<'hir>) -> Ty<'hir> {
        struct Instantiator<'a> {
            ctxt: &'a HirCtxt<'a>,
            subs: Map<Ident, Ty<'a>>,
        }

        impl<'a> Folder<'a, Ty<'a>> for Instantiator<'a> {
            fn ctxt(&self) -> &'a HirCtxt<'a> {
                self.ctxt
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
            ctxt: self.hir_ctxt,
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
            ctxt: &'a HirCtxt<'a>,
        }

        impl<'a> Folder<'a, Ty<'a>> for SkolemReplacer<'a> {
            fn ctxt(&self) -> &'a HirCtxt<'a> {
                self.ctxt
            }

            fn fold(&mut self, typ: Ty<'a>) -> Ty<'a> {
                if let TyKind::Var(var) = typ.kind() {
                    Ty::skolem(self.ctxt, self.skolems[var])
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
            ctxt: self.hir_ctxt,
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

    fn infer_solve_expr(&mut self, expr: &'hir Expr<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        let res = self.infer_expr(expr)?;
        self.solve_current()?;
        let res = self.generalize(res);
        Ok(res)
    }

    fn infer_comp_unit(&mut self, unit: &'hir CompUnit<'hir>) -> Result<(), InferError<'hir>> {
        let mexpr = self.hir_ctxt.arena.alloc(ModExpr {
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
                    self.hir_ctxt.set_type(value.path.res().hir_id(), typ);
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

    fn infer_expr(&mut self, expr: &'hir Expr<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        Ok(match expr.kind {
            // NB. Applications are either function calls (such as `(f a b ...)`)
            //     or "0-arity" applications, i.e., paths.
            ExprKind::Call(..) | ExprKind::Path(_) | ExprKind::Constructor(_) => {
                let (head, args) = match expr.kind {
                    ExprKind::Call(_, head, args) => (head, args),
                    ExprKind::Path(_) | ExprKind::Constructor(_) => (expr, &[] as &[_]),
                    _ => unreachable!(),
                };
                let head_typ = match head.kind {
                    ExprKind::Path(p) | ExprKind::Constructor(p) => self.infer_path(p),
                    _ => self.infer_expr(head),
                }?;
                let mut typ = self.instantiate(head_typ);
                for arg in args {
                    if let TyKind::Arrow(_, arg_typ, ret_typ) = *typ.kind() {
                        self.check_expr(arg, arg_typ)?;
                        typ = ret_typ;
                    } else {
                        break;
                    }
                }
                typ
            }
            ExprKind::External(_, typ) => typ,
            ExprKind::Lit(l) => self.type_from_lit(l, expr.span),
            ExprKind::Lambda(lambda) => self.infer_lambda(lambda.args, lambda.body)?,
            ExprKind::Let(binds, body) => {
                for bind in binds {
                    let pat_typ = self.infer_pat(&bind.0)?;
                    let bind_typ = self.infer_expr(&bind.1)?;
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
                for elem in elems {
                    typs.push(self.infer_expr(elem)?);
                }
                Ty::tuple(self.hir_ctxt, typs, expr.span)
            }
            ExprKind::Vector(elems) => {
                let base_typ = self.fresh_var();
                for elem in elems {
                    let elem_typ = self.infer_expr(elem)?;
                    self.constrain(base_typ, elem_typ);
                }
                self.hir_ctxt.typ(TyKind::Vector(base_typ), expr.span)
            }
            ExprKind::Seq(e1, e2) => {
                self.check_expr(
                    e1,
                    self.hir_ctxt
                        .typ(TyKind::Base(BaseType::Unit), Span::dummy()),
                )?;
                self.infer_expr(e2)?
            }
            ExprKind::Case(scrutinee, arms) => {
                let typ = self.infer_expr(scrutinee)?;
                let var = self.fresh_var();
                for arm in arms {
                    let pat_typ = self.infer_pat(&arm.0)?;
                    self.constrain(typ, pat_typ);
                    let arm_typ = self.infer_expr(&arm.1)?;
                    self.constrain(var, arm_typ);
                }
                var
            }
            ExprKind::If(cond, then_expr, else_expr) => {
                self.check_expr(
                    cond,
                    self.hir_ctxt
                        .typ(TyKind::Base(BaseType::Bool), Span::dummy()),
                )?;
                let then_typ = self.infer_expr(then_expr)?;
                let else_typ = self.infer_expr(else_expr)?;
                self.constrain(then_typ, else_typ);
                then_typ
            }
        })
    }

    /// Infer the type of a lambda expression `(\args -> body)`.
    fn infer_lambda(
        &mut self,
        args: &'hir [Pat<'hir>],
        body: &'hir Expr<'hir>,
    ) -> Result<Ty<'hir>, InferError<'hir>> {
        if let Some((first, rest)) = args.split_first() {
            let arg_typ = self.infer_pat(first)?;
            let ret_typ = self.infer_lambda(rest, body)?;
            Ok(Ty::arrow(self.hir_ctxt, NO_WEB, arg_typ, ret_typ))
        } else {
            self.infer_expr(body)
        }
    }

    /// Infer the type of a path by looking it up in the environment.
    fn infer_path(&mut self, path: Path<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        let hir_id = path.res().hir_id();
        Ok(match self.hir_ctxt.get_type(hir_id) {
            Some(typ) => typ,
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
                        self.fresh_var()
                    } else {
                        match value.typ {
                            Some(typ) => {
                                self.check_expr(value.expr, typ)?;
                                typ
                            }
                            None => self.infer_expr(value.expr)?,
                        }
                    }
                };
                self.hir_ctxt.set_type(hir_id, typ);
                typ
            }
        })
    }

    /// Infer a type for a pattern.
    fn infer_pat(&mut self, pat: &'hir Pat<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        Ok(match pat.kind {
            PatKind::Wild => self.fresh_var(),
            PatKind::Var(path) => {
                let var = self.fresh_var();
                self.hir_ctxt.set_type(path.res().hir_id(), var);
                var
            }
            PatKind::Lit(l) => self.type_from_lit(l, pat.span),
            PatKind::Ann(pat, typ) => {
                self.check_pat(pat, typ)?;
                typ
            }
            PatKind::Tuple(pats) => Ty::tuple(self.hir_ctxt, self.infer_pats(pats)?, pat.span),
            PatKind::Constructor(cons, args) => {
                // TODO. well-formed check for cons_t
                let cons_typ = self.infer_path(cons)?;
                if args.is_empty() {
                    cons_typ
                } else {
                    let arg_typs = self.infer_pats(args)?;
                    let ret_typ = self.fresh_var();
                    let cons_typ = self.instantiate(cons_typ);
                    self.constrain(Ty::n_arrow(self.hir_ctxt, arg_typs, ret_typ), cons_typ);
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
    fn check_expr(
        &mut self,
        expr: &'hir Expr<'hir>,
        expected: Ty<'hir>,
    ) -> Result<(), InferError<'hir>> {
        //let expected = self.skolemize(expected);
        match (expr.kind, expected.kind()) {
            (ExprKind::Lit(l), TyKind::Base(b)) if l.base_type() == *b => (),
            (ExprKind::Lit(l), TyKind::Var(_)) => {
                self.constrain(expected, self.type_from_lit(l, expr.span));
            }

            // TODO. these branches probably aren't necessary
            (ExprKind::Lambda(lambda), TyKind::Uni(_)) => {
                let mut arg_typs = Vec::with_capacity(lambda.args.len());
                let ret_typ =
                    self.check_lambda_var(lambda.args, lambda.body, expected, &mut arg_typs)?;
                self.constrain(expected, Ty::n_arrow(self.hir_ctxt, arg_typs, ret_typ));
            }
            (ExprKind::Lambda(lambda), TyKind::Arrow(..)) => {
                self.check_lambda_arrow(lambda.args, lambda.body, expected)?
            }

            (ExprKind::Tuple(es), TyKind::Tuple(ts)) => {
                if es.len() == ts.len() {
                    for (e, &t) in es.iter().zip(*ts) {
                        self.check_expr(e, t)?;
                    }
                } else {
                    return Err(InferError::ExprTupleLength(expr.span, es.len(), ts.len()));
                }
            }
            (ExprKind::Case(scrutinee, arms), _) => {
                let typ = self.infer_expr(scrutinee)?;
                for arm in arms {
                    let pat_typ = self.infer_pat(&arm.0)?;
                    self.constrain(typ, pat_typ);
                    let arm_typ = self.infer_expr(&arm.1)?;
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
        body: &'hir Expr<'hir>,
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
        body: &'hir Expr<'hir>,
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
            (PatKind::Var(path), _) => {
                self.hir_ctxt.set_type(path.res().hir_id(), expected);
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
