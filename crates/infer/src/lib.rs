#![feature(never_type)]
#![feature(let_chains)]

use base::hash::Map;
use span::{Ident, Sp, Span, Sym, diag::Diagnostic};
use syntax::ast::*;

mod error;
mod resolve;
mod substitution;
mod unify;

use error::InferError;
use substitution::Substitution;
use ty::{Skolem, SkolemId, Ty, TyCtxt, TyKind, TypeFolder, TypeVar};
use unify::Origin;

pub mod ty;
pub use resolve::{Constructor, Res, ResId, Resolution, Value};

pub fn infer_program_in<'ast, 't>(
    ctxt: &'t TyCtxt<'t>,
    program: &'ast Program<'ast>,
) -> Result<(&'t Resolution<'t>, &'t Environment<'t>), Diagnostic> {
    let res = resolve::resolve_program_in(ctxt, program)?;
    let res = ctxt.arena.alloc(res);
    Infer::new(ctxt, program, res)
        .infer()
        .map_err(Diagnostic::from)
}

#[derive(Default)]
pub struct Environment<'t> {
    pub res: Map<Res, Ty<'t>>,
    pub ast: Map<AstId, Ty<'t>>,
}

struct Infer<'ast, 't> {
    ctxt: &'t TyCtxt<'t>,
    program: &'ast Program<'ast>,
    res: &'t Resolution<'t>,
    env: Environment<'t>,
    subs: Substitution<'t>,

    bool_ty: Ty<'t>,
    unit_ty: Ty<'t>,
    skolem: SkolemId,
}

impl<'ast, 't> Infer<'ast, 't> {
    fn new(ctxt: &'t TyCtxt<'t>, program: &'ast Program<'ast>, res: &'t Resolution<'t>) -> Self {
        Self {
            ctxt,
            program,
            res,
            env: Environment::default(),
            subs: Substitution::new(ctxt),

            bool_ty: Ty::new(ctxt, TyKind::Base(BaseType::Bool)),
            unit_ty: Ty::new(ctxt, TyKind::Base(BaseType::Unit)),
            skolem: SkolemId::ZERO,
        }
    }

    fn infer(mut self) -> Result<(&'t Resolution<'t>, &'t Environment<'t>), InferError<'t>> {
        self.infer_comp_unit(self.program.unit)?;
        let main_ty = self.infer_expr(self.program.main)?;
        log::trace!("main : {main_ty}");
        Ok((self.res, self.ctxt.arena.alloc(self.env)))
    }

    fn type_from_lit(&self, lit: Lit) -> Ty<'t> {
        Ty::new(self.ctxt, TyKind::Base(lit.base_type()))
    }

    fn fresh_var(&self) -> Ty<'t> {
        self.subs.new_var()
    }

    /// Generalize a type over its unification variables.
    ///
    /// For example, `generalize('1 -> '1) = 'a -> 'a`.
    fn generalize(&self, ty: Ty<'t>) -> Ty<'t> {
        let mut char_count = 0;
        let mut fresh = || {
            let ch = (b'a' + char_count) as char;
            char_count = (char_count + 1) % (b'z' - b'a');
            let id = Ident::new(Sym::intern(&format!("'{ch}")), Span::dummy());
            TypeVar::new(id)
        };
        let ty = self.subs.apply(ty);
        let free_vars = ty.uni_vars();
        if !free_vars.is_empty() {
            for var in free_vars {
                self.subs.insert(var.id, Ty::type_var(self.ctxt, fresh()));
            }
            self.subs.apply(ty)
        } else {
            ty
        }
    }

    fn instantiate(&self, ty: Ty<'t>) -> Ty<'t> {
        struct Instantiator<'t> {
            ctxt: &'t TyCtxt<'t>,
            subs: Map<Ident, Ty<'t>>,
        }

        impl<'t> TypeFolder<'t> for Instantiator<'t> {
            fn ctxt(&self) -> &'t TyCtxt<'t> {
                self.ctxt
            }

            fn fold(&mut self, ty: Ty<'t>) -> Ty<'t> {
                if let TyKind::Var(var) = ty.kind()
                    && let Some(&other) = self.subs.get(&var.name)
                {
                    other
                } else {
                    ty.fold_with(self)
                }
            }
        }

        Instantiator {
            ctxt: self.ctxt,
            subs: ty
                .type_vars()
                .iter()
                .map(|&var| (var.name, self.fresh_var()))
                .collect(),
        }
        .fold(ty)
    }

    fn fresh_skolem(&mut self) -> SkolemId {
        let id = self.skolem;
        self.skolem = self.skolem + 1;
        id
    }

    fn skolemize(&mut self, ty: Ty<'t>) -> Ty<'t> {
        struct SkolemReplacer<'t> {
            skolems: Map<TypeVar, Skolem>,
            ctxt: &'t TyCtxt<'t>,
        }

        impl<'t> TypeFolder<'t> for SkolemReplacer<'t> {
            fn ctxt(&self) -> &'t TyCtxt<'t> {
                self.ctxt
            }

            fn fold(&mut self, ty: Ty<'t>) -> Ty<'t> {
                if let TyKind::Var(var) = ty.kind() {
                    let skolem = self.skolems[var];
                    Ty::new(self.ctxt(), TyKind::Skolem(skolem))
                } else {
                    ty.fold_with(self)
                }
            }
        }

        SkolemReplacer {
            ctxt: self.ctxt,
            skolems: ty
                .type_vars()
                .iter()
                .map(|&var| (var, Skolem::new(self.fresh_skolem(), var.name)))
                .collect(),
        }
        .fold(ty)
    }

    fn infer_comp_unit(&mut self, unit: &'ast CompUnit<'ast>) -> Result<(), InferError<'t>> {
        self.infer_items(unit.items)
    }

    fn infer_items(&mut self, items: &'ast [Sp<Item<'ast>>]) -> Result<(), InferError<'t>> {
        log::trace!("{{");
        log::block_in();
        for item in items {
            match item.value {
                Item::Type(..) => (),
                Item::Value(id, ast_ty, expr) => {
                    let res = self.res[id.ast_id];
                    let value =
                        self.res.values.get(&res.res_id()).unwrap_or_else(|| {
                            panic!("ICE: expected '{id}' to be resolved to {res}")
                        });
                    let ty = if value.recursive {
                        // FIXME
                        self.fresh_var()
                    } else {
                        match value.ty {
                            Some(ty) => {
                                // Suppose we have a silly declaration like val id x : 'a -> 'a = ().
                                //
                                // Without skolemization of 'a -> 'a, we have the following:
                                //
                                //   ('0 -> ()) ~ ('a -> 'a) -- infer \x -> () and equate with 'a -> 'a
                                //   ('0 -> ()) ~ ('1 -> '1) -- instantiate 'a -> 'a to '1 -> '1
                                //   ('0 ~ '1) /\ (() ~ '1)  -- destruct arrow
                                //
                                // ==> '0 == '1 == (), and we succeed...oops.
                                //
                                // With skolemization of 'a -> 'a to #'a -> #'a, #'a cannot unify with ().
                                let skol_ty = self.skolemize(ty);
                                self.check_expr(
                                    expr,
                                    skol_ty,
                                    Origin::Generic(expr.span, ast_ty.unwrap().span()),
                                )?;
                                ty
                            }
                            None => {
                                let ty = self.infer_expr(expr)?;
                                self.generalize(ty)
                            }
                        }
                    };
                    log::trace!("{id} : {ty}");
                    self.env.res.insert(res, ty);
                }
                Item::Mod(id, mexpr) => {
                    log::trace!("mod {id}");
                    self.infer_mod_expr(mexpr)?;
                }
            }
        }
        log::block_out();
        log::trace!("}}");
        Ok(())
    }

    fn infer_mod_expr(&mut self, mexpr: &'ast Sp<ModExpr<'ast>>) -> Result<(), InferError<'t>> {
        match mexpr.value {
            ModExpr::Import(source_id) => {
                let comp_unit = self
                    .program
                    .imports
                    .get(&source_id)
                    .expect("HIR lowering produced an invalid source_id for an import");
                self.infer_comp_unit(comp_unit)
            }
            ModExpr::Path(_path) => {
                todo!()
            }
            ModExpr::Struct(items) => self.infer_items(items),
        }
    }

    fn infer_expr(&mut self, expr: &'ast Expr<'ast>) -> Result<Ty<'t>, InferError<'t>> {
        let ty = match expr.kind {
            ExprKind::Call(..) | ExprKind::Path(_) | ExprKind::Constructor(_) => {
                let (head, args) = match expr.kind {
                    ExprKind::Call(head, args) => (head, args),
                    ExprKind::Path(_) | ExprKind::Constructor(_) => (expr, &[] as &[_]),
                    _ => unreachable!(),
                };
                let head_ty = match head.kind {
                    ExprKind::Path(p) => {
                        // FIXME query defining span
                        let res = self.res[p.ast_id];
                        Ok(self.env.res[&res])
                    }
                    ExprKind::Constructor(p) => self.infer_constructor(p),
                    _ => self.infer_expr(head),
                }?;
                let mut arg_tys = Vec::new();
                for arg in args {
                    let arg_ty = self.infer_expr(arg)?;
                    arg_tys.push(arg_ty);
                }
                let ret_ty = self.fresh_var();
                self.eq(
                    Origin::Generic(head.span, Span::dummy()),
                    Ty::n_arrow(self.ctxt, arg_tys, ret_ty),
                    head_ty,
                )?;
                ret_ty
            }
            ExprKind::External(_) => unreachable!(),
            ExprKind::Lit(l) => self.type_from_lit(l),
            ExprKind::Lambda(lambda) => {
                let arg_tys = self.infer_pats(lambda.args)?;
                let body_ty = self.infer_expr(lambda.body)?;
                Ty::n_arrow(self.ctxt, arg_tys, body_ty)
            }
            ExprKind::Let(binds, body) => {
                for (pat, bind) in binds {
                    let pat_ty = self.infer_pat(pat)?;
                    let bind_ty = self.infer_expr(bind)?;
                    self.eq(Origin::Generic(pat.span, bind.span), pat_ty, bind_ty)?;
                }
                self.infer_expr(body)?
            }
            ExprKind::Ann(e, t) => {
                let expected = self.res.annotations[&expr.ast_id];
                let expected = self.skolemize(expected);
                self.check_expr(e, expected, Origin::Generic(e.span, t.span))?;
                expected
            }
            ExprKind::Tuple(elems) => {
                let mut tys = Vec::with_capacity(elems.len());
                for elem in elems {
                    tys.push(self.infer_expr(elem)?);
                }
                Ty::tuple(self.ctxt, tys)
            }
            ExprKind::Vector(elems) => {
                let vector_base_ty = self.fresh_var();
                for elem in elems {
                    let elem_ty = self.infer_expr(elem)?;
                    self.eq(
                        Origin::Vector {
                            vector_span: expr.span,
                            elem_span: elem.span,
                        },
                        vector_base_ty,
                        elem_ty,
                    )?;
                }
                Ty::new(self.ctxt, TyKind::Vector(vector_base_ty))
            }
            ExprKind::Case(scrutinee, arms) => {
                let scrutinee_ty = self.infer_expr(scrutinee)?;
                let var = self.fresh_var();
                for (pat, arm) in arms {
                    let pat_ty = self.infer_pat(pat)?;
                    self.eq(
                        Origin::Generic(scrutinee.span, pat.span),
                        scrutinee_ty,
                        pat_ty,
                    )?;
                    let arm_ty = self.infer_expr(arm)?;
                    self.eq(Origin::Generic(expr.span, arm.span), var, arm_ty)?;
                }
                var
            }
            ExprKind::If(cond, then_expr, else_expr) => {
                self.check_expr(cond, self.bool_ty, Origin::If(cond.span))?;
                let then_ty = self.infer_expr(then_expr)?;
                let else_ty = self.infer_expr(else_expr)?;
                self.eq(
                    Origin::Generic(then_expr.span, else_expr.span),
                    then_ty,
                    else_ty,
                )?;
                then_ty
            }
            ExprKind::Seq(e1, e2) => {
                self.check_expr(e1, self.unit_ty, Origin::Seq(e1.span))?;
                self.infer_expr(e2)?
            }
        };
        self.env.ast.insert(expr.ast_id, ty);
        Ok(ty)
    }

    fn infer_constructor(&self, path: Path<'ast>) -> Result<Ty<'t>, InferError<'t>> {
        let res = self.res[path.ast_id];
        Ok(self.res.constructors[&res.res_id()].ty)
    }

    /// Infer a type for a pattern.
    fn infer_pat(&mut self, pat: &'ast Pat<'ast>) -> Result<Ty<'t>, InferError<'t>> {
        let ty = match pat.kind {
            PatKind::Wild => self.fresh_var(),
            PatKind::Var(id) => {
                let var = self.fresh_var();
                let res = self.res[id.ast_id];
                self.env.res.insert(res, var);
                var
            }
            PatKind::Lit(l) => self.type_from_lit(l),
            PatKind::Ann(p, t) => {
                let expected = self.res.annotations[&pat.ast_id];
                let expected = self.skolemize(expected);
                match p.kind {
                    PatKind::Wild => (),
                    _ => {
                        let ty = self.infer_pat(p)?;
                        self.eq(Origin::Generic(p.span, t.span), ty, expected)?;
                    }
                }
                expected
            }
            PatKind::Tuple(pats) => Ty::tuple(self.ctxt, self.infer_pats(pats)?),
            PatKind::Constructor(cons, args) => {
                let cons_ty = self.infer_constructor(cons)?;
                if args.is_empty() {
                    cons_ty
                } else {
                    let arg_tys = self.infer_pats(args)?;
                    let ret_ty = self.fresh_var();
                    self.eq(
                        Origin::Generic(pat.span, cons.span()),
                        Ty::n_arrow(self.ctxt, arg_tys, ret_ty),
                        cons_ty,
                    )?;
                    ret_ty
                }
            }
            PatKind::Or(_pats) => todo!("implement or patterns"),
        };
        self.env.ast.insert(pat.ast_id, ty);
        Ok(ty)
    }

    fn infer_pats(&mut self, pats: &'ast [Pat<'ast>]) -> Result<Vec<Ty<'t>>, InferError<'t>> {
        let mut tys = Vec::with_capacity(pats.len());
        for pat in pats {
            tys.push(self.infer_pat(pat)?);
        }
        Ok(tys)
    }

    fn check_expr(
        &mut self,
        expr: &'ast Expr<'ast>,
        expected: Ty<'t>,
        origin: Origin,
    ) -> Result<(), InferError<'t>> {
        match (expr.kind, expected.kind()) {
            (ExprKind::External(_), _) => (),
            (ExprKind::Lit(l), TyKind::Base(b)) if l.base_type() == *b => (),
            (ExprKind::Case(scrutinee, arms), _) => {
                let scrutinee_ty = self.infer_expr(scrutinee)?;
                for (pat, arm) in arms {
                    let pat_ty = self.infer_pat(pat)?;
                    self.eq(
                        Origin::Generic(scrutinee.span, pat.span),
                        scrutinee_ty,
                        pat_ty,
                    )?;
                    let arm_ty = self.infer_expr(arm)?;
                    self.eq(origin, arm_ty, expected)?;
                }
            }
            (_, _) => {
                let ty = self.infer_expr(expr)?;
                self.eq(origin, ty, expected)?;
            }
        }
        Ok(())
    }
}
