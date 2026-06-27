#![feature(never_type)]

use std::fmt;

use base::hash::Map;
use span::{Ident, Span, Sym, diag::Diagnostic};
use syntax::ast;

mod error;
mod match_compile;
mod module_graph;
mod pretty;
mod resolve;
mod substitution;
mod unify;

use error::InferError;
use substitution::Substitution;
use ty::{Skolem, SkolemId, Ty, TyCtxt, TyKind, TypeFolder, TypeVar};
use unify::Origin;

pub mod hir;
pub mod ty;

use hir::*;

pub fn infer_program_in<'ast, 't>(
    ctxt: &'t TyCtxt<'t>,
    program: &'ast ast::Program<'ast>,
) -> Result<Program<'t>, Diagnostic> {
    let mut hir = resolve::resolve_program_in(ctxt, program)?;

    Infer::new(ctxt).infer(&mut hir).map_err(Diagnostic::from)?;

    match_compile::compile(&ctxt, &mut hir)?;

    Ok(hir)
}

struct Infer<'t> {
    ctxt: &'t TyCtxt<'t>,

    subs: Substitution<'t>,

    variables: Map<Res, Ty<'t>>,

    bool_ty: Ty<'t>,
    unit_ty: Ty<'t>,

    skolem: SkolemId,
}

impl<'t> Infer<'t> {
    fn new(ctxt: &'t TyCtxt<'t>) -> Self {
        Self {
            ctxt,
            subs: Substitution::new(ctxt),
            variables: Map::default(),
            bool_ty: Ty::new(ctxt, TyKind::Base(ast::BaseType::Bool)),
            unit_ty: Ty::new(ctxt, TyKind::Base(ast::BaseType::Unit)),
            skolem: SkolemId::ZERO,
        }
    }

    fn infer(mut self, program: &mut Program<'t>) -> Result<(), InferError<'t>> {
        for import in program.imports.values_mut() {
            self.infer_comp_unit(import)?;
        }
        self.infer_comp_unit(&mut program.unit)?;
        {
            let main_ty = self.infer_expr(&mut program.main)?;
            program.main.typ.replace(self.generalize(main_ty));
        }

        struct ApplyFinalSubstitution<'a, 't> {
            subs: &'a Substitution<'t>,
        }

        impl<'a, 't> HirVisitor<'t> for ApplyFinalSubstitution<'a, 't> {
            fn visit_var(&mut self, var: &mut Var<'t>) {
                assert!(var.typ.is_some(), "variable {var} has no type");
                if let Some(typ) = var.typ.as_mut() {
                    *typ = self.subs.apply(*typ);
                    assert!(
                        typ.uni_vars().is_empty(),
                        "unexpected unification variables in {typ}"
                    );
                } else {
                    panic!("variable {var} has no type");
                }
            }

            fn visit_expr(&mut self, expr: &mut Expr<'t>) {
                if let Some(typ) = expr.typ.as_mut() {
                    *typ = self.subs.apply(*typ);
                    assert!(
                        typ.uni_vars().is_empty(),
                        "unexpected unification variables in {typ}"
                    );
                } else {
                    panic!("expression {expr:?} has no type");
                }
                expr.visit_with(self);
            }

            fn visit_pat(&mut self, pat: &mut Pat<'t>) {
                if let Some(typ) = pat.typ.as_mut() {
                    *typ = self.subs.apply(*typ);
                    assert!(
                        typ.uni_vars().is_empty(),
                        "unexpected unification variables in {typ}"
                    );
                } else {
                    panic!("pattern {pat:?} has no type");
                }
                pat.visit_with(self);
            }
        }

        let mut applier = ApplyFinalSubstitution { subs: &self.subs };
        applier.visit_program(program);

        log::trace!("main : {}", program.main.typ.unwrap());
        Ok(())
    }

    fn type_from_lit(&self, lit: ast::Lit) -> Ty<'t> {
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

        let skol_ty = SkolemReplacer {
            ctxt: self.ctxt,
            skolems: ty
                .type_vars()
                .iter()
                .map(|&var| (var, Skolem::new(self.fresh_skolem(), var.name)))
                .collect(),
        }
        .fold(ty);

        log::trace!("[skolemize] {ty} to {skol_ty}");
        skol_ty
    }

    fn infer_comp_unit(&mut self, unit: &mut CompUnit<'t>) -> Result<(), InferError<'t>> {
        self.infer_items(&mut unit.items)
    }

    fn infer_items(&mut self, items: &mut Vec<Item<'t>>) -> Result<(), InferError<'t>> {
        log::trace!("{{");
        log::block_in();
        for item in items.iter_mut() {
            match item {
                Item::Expr {
                    var,
                    recursive,
                    expr,
                    expected_typ,
                    typ,
                } => {
                    log::trace!("[infer item] {var} recursive={recursive}");
                    assert!(typ.is_none());
                    let ty = if *recursive {
                        // FIXME
                        self.fresh_var()
                    } else {
                        match expected_typ {
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
                                let skol_ty = self.skolemize(ty.value);
                                self.check_expr(
                                    expr,
                                    skol_ty,
                                    Origin::Generic(expr.span, ty.span()),
                                )?;
                                ty.value
                            }
                            None => {
                                let ty = self.infer_expr(expr)?;
                                self.generalize(ty)
                            }
                        }
                    };
                    expr.typ = Some(ty);
                    *typ = Some(ty);
                    self.variables.insert(var.res, ty);
                }
            }
        }
        log::block_out();
        log::trace!("}}");
        Ok(())
    }

    fn infer_var(&mut self, var: &mut Var<'t>) -> Ty<'t> {
        let typ = match &mut var.typ {
            Some(typ) => *typ,
            None => {
                let typ = *self
                    .variables
                    .get(&var.res)
                    .unwrap_or_else(|| panic!("no type for var {var}"));
                var.typ = Some(typ);
                typ
            }
        };
        log::trace!("[infer_var] {var} : {typ}");
        typ
    }

    fn infer_expr(&mut self, expr: &mut Expr<'t>) -> Result<Ty<'t>, InferError<'t>> {
        log::trace!("[infer_expr] {expr}");
        log::block_in();

        let ty = match &mut expr.kind {
            ExprKind::Var(v) => self.infer_var(v),
            ExprKind::Call(head, args) => {
                let head_span = head.span;
                let head_ty = self.infer_expr(head)?;

                let mut arg_tys = Vec::new();
                for arg in args.iter_mut() {
                    let arg_ty = self.infer_expr(arg)?;
                    arg_tys.push(arg_ty);
                }

                let ret_ty = self.fresh_var();
                self.eq(
                    Origin::Generic(head_span, Span::dummy()),
                    Ty::n_arrow(self.ctxt, arg_tys, ret_ty),
                    head_ty,
                )?;
                ret_ty
            }
            ExprKind::ExternalCall(ext_var, args) => {
                let mut arg_typs = Vec::with_capacity(args.len());
                for arg in args.iter_mut() {
                    arg_typs.push(self.infer_var(arg));
                }

                let ret_ty = self.fresh_var();
                self.eq(
                    Origin::Generic(ext_var.span, Span::dummy()),
                    Ty::n_arrow(self.ctxt, arg_typs, ret_ty),
                    ext_var.typ.expect("external without type"),
                )?;
                ret_ty
            }
            ExprKind::Cons(cons_var, args) => {
                let cons_typ = cons_var.typ.expect("no type for constructor");
                log::trace!("Checking {cons_var} with type {cons_typ}");

                let cons = self.ctxt.get_constructor(cons_var.res).unwrap();

                assert_eq!(args.len(), cons.args.len());

                let mut arg_tys = Vec::new();
                for (arg, expected_arg) in args.iter_mut().zip(cons.args) {
                    let arg_ty = self.infer_expr(arg)?;
                    self.eq(Origin::ConsArg(arg.span), arg_ty, *expected_arg)?;
                    arg_tys.push(arg_ty);
                }

                let ret_ty = self.fresh_var();
                self.eq(
                    Origin::Generic(cons_var.span, Span::dummy()),
                    Ty::n_arrow(self.ctxt, arg_tys, ret_ty),
                    cons_typ,
                )?;
                ret_ty
            }
            ExprKind::Lit(l) => self.type_from_lit(*l),
            ExprKind::Lambda(lambda) => {
                let arg_tys = self.infer_pats(lambda.args.as_mut())?;
                let body_ty = self.infer_expr(lambda.body.as_mut())?;
                Ty::n_arrow(self.ctxt, arg_tys, body_ty)
            }
            ExprKind::Let(binds, body) => {
                for (pat, bind) in binds {
                    let pat_span = pat.span;
                    let pat_ty = self.infer_pat(pat)?;

                    let bind_span = bind.span;
                    let bind_ty = self.infer_expr(bind)?;

                    self.eq(Origin::Generic(pat_span, bind_span), pat_ty, bind_ty)?;
                }
                self.infer_expr(body.as_mut())?
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
                    let elem_span = elem.span;
                    let elem_ty = self.infer_expr(elem)?;
                    self.eq(
                        Origin::Vector {
                            vector_span: expr.span,
                            elem_span,
                        },
                        vector_base_ty,
                        elem_ty,
                    )?;
                }
                Ty::new(self.ctxt, TyKind::Vector(vector_base_ty))
            }
            ExprKind::Case(scrutinee, arms, _) => {
                let scrutinee_span = scrutinee.span;
                let scrutinee_ty = self.infer_expr(scrutinee.as_mut())?;
                let var = self.fresh_var();
                for (pat, arm) in arms {
                    let pat_span = pat.span;
                    let pat_ty = self.infer_pat(pat)?;
                    self.eq(
                        Origin::Generic(scrutinee_span, pat_span),
                        scrutinee_ty,
                        pat_ty,
                    )?;

                    let arm_span = arm.span;
                    let arm_ty = self.infer_expr(arm)?;
                    self.eq(Origin::Generic(expr.span, arm_span), var, arm_ty)?;
                }
                var
            }
            ExprKind::If(cond_expr, then_expr, else_expr) => {
                let cond_span = cond_expr.span;
                let then_span = then_expr.span;
                let else_span = else_expr.span;
                self.check_expr(cond_expr.as_mut(), self.bool_ty, Origin::If(cond_span))?;
                let then_ty = self.infer_expr(then_expr.as_mut())?;
                let else_ty = self.infer_expr(else_expr.as_mut())?;
                self.eq(Origin::Generic(then_span, else_span), then_ty, else_ty)?;
                then_ty
            }
            ExprKind::Seq(e1, e2) => {
                let span = e1.span;
                self.check_expr(e1.as_mut(), self.unit_ty, Origin::Seq(span))?;
                self.infer_expr(e2.as_mut())?
            }
        };
        expr.typ = Some(ty);

        log::trace!("[result] {ty}");
        log::block_out();
        Ok(ty)
    }

    /// Infer a type for a pattern.
    fn infer_pat(&mut self, pat: &mut Pat<'t>) -> Result<Ty<'t>, InferError<'t>> {
        log::trace!("[infer_pat] {pat}");
        log::block_in();

        let ty = match &mut pat.kind {
            PatKind::Wild => self.fresh_var(),
            PatKind::Var(id) => {
                let var = self.fresh_var();
                id.typ = Some(var);
                self.variables.insert(id.res, var);
                var
            }
            PatKind::Lit(l) => self.type_from_lit(*l),
            PatKind::Tuple(pats) => Ty::tuple(self.ctxt, self.infer_pats(pats)?),
            PatKind::Cons(cons_var, args) => {
                let cons_typ = cons_var.typ.unwrap();
                if args.is_empty() {
                    cons_typ
                } else {
                    let cons = self.ctxt.get_constructor(cons_var.res).unwrap();

                    assert_eq!(args.len(), cons.args.len());

                    let mut arg_tys = Vec::new();
                    for (arg, expected_arg) in args.iter_mut().zip(cons.args) {
                        let arg_ty = self.infer_pat(arg)?;
                        self.eq(
                            Origin::Generic(arg.span, Span::dummy()),
                            arg_ty,
                            *expected_arg,
                        )?;
                        arg_tys.push(arg_ty);
                    }

                    let ret_ty = self.fresh_var();
                    self.eq(
                        Origin::Generic(cons_var.span, Span::dummy()),
                        Ty::n_arrow(self.ctxt, arg_tys, ret_ty),
                        cons_typ,
                    )?;
                    ret_ty
                }
            }
            PatKind::Or(_pats) => todo!("implement or patterns"),
        };
        pat.typ = Some(ty);

        log::trace!("[result] {ty}");
        log::block_out();
        Ok(ty)
    }

    fn infer_pats(&mut self, pats: &mut Vec<Pat<'t>>) -> Result<Vec<Ty<'t>>, InferError<'t>> {
        let mut tys = Vec::with_capacity(pats.len());
        for pat in pats {
            tys.push(self.infer_pat(pat)?);
        }
        Ok(tys)
    }

    fn check_expr(
        &mut self,
        expr: &mut Expr<'t>,
        expected: Ty<'t>,
        origin: Origin,
    ) -> Result<(), InferError<'t>> {
        log::trace!("[check_expr] {expr} : {expected} @ {origin:?}");
        log::block_in();

        match (&mut expr.kind, expected.kind()) {
            (ExprKind::Lit(l), TyKind::Base(b)) if l.base_type() == *b => (),
            (ExprKind::Case(scrutinee, arms, _), _) => {
                let scrutinee_span = scrutinee.span;
                let scrutinee_ty = self.infer_expr(scrutinee)?;
                for (pat, arm) in arms {
                    let pat_span = pat.span;
                    let pat_ty = self.infer_pat(pat)?;
                    self.eq(
                        Origin::Generic(scrutinee_span, pat_span),
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
        expr.typ = Some(expected);

        log::block_out();
        Ok(())
    }
}

base::newtype_index! {
    pub struct ResId {}
}

impl fmt::Display for ResId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.index())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Res {
    Def(DefKind, ResId),
    Local(ResId),
}

impl Res {
    pub fn res_id(&self) -> ResId {
        match *self {
            Res::Def(_, res_id) | Res::Local(res_id) => res_id,
        }
    }

    pub fn dummy() -> Self {
        Res::Local(ResId::ZERO)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum DefKind {
    Value,
    Type,
    Cons,
}

impl fmt::Display for Res {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Res::Def(kind, res_id) => {
                write!(f, "{kind:?}:{res_id}")
            }
            Res::Local(res_id) => res_id.fmt(f),
        }
    }
}
