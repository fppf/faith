#![feature(never_type)]
#![feature(let_chains)]
#![allow(unused)]

use base::hash::Map;
use resolve::{Res, ResId, Resolution};
use span::{Ident, Sp, Span, Sym, diag::Diagnostic};
use syntax::ast::*;

mod constraint;
mod substitution;
mod typ;
mod unify;

pub mod error;
pub mod resolve;

use constraint::Constraint;
use error::InferError;
use substitution::Substitution;
use typ::{Folder, Skolem, SkolemId, Ty, TyKind, TypeVar};

base::declare_arena!('t, []);

pub struct TyCtxt<'t> {
    pub arena: Arena<'t>,
}

impl Default for TyCtxt<'_> {
    fn default() -> Self {
        Self {
            arena: Arena::default(),
        }
    }
}

impl<'t> TyCtxt<'t> {
    pub fn typ(&'t self, kind: TyKind<'t>, span: Span) -> Ty<'t> {
        Ty::new(self, kind, span)
    }
}

pub fn infer_program_in<'ast, 't>(
    ctxt: &'t TyCtxt<'t>,
    program: &'ast Program<'ast>,
) -> Result<(), Diagnostic> {
    let res = resolve::resolve_program_in(ctxt, program)?;
    TypeChecker::new(ctxt, program, &res)
        .infer()
        .map_err(Diagnostic::from)
}

struct TypeChecker<'ast, 't> {
    ctxt: &'t TyCtxt<'t>,
    program: &'ast Program<'ast>,
    env: Map<Res, Ty<'t>>,
    res: &'t Resolution<'ast, 't>,

    type_var_src: TypeVarSource,
    skolem: SkolemId,
    constraints: Vec<Constraint<'t, Ty<'t>>>,
    subs: Substitution<'t, Ty<'t>>,
}

#[derive(Default)]
struct TypeVarSource {
    char_count: u8,
}

impl TypeVarSource {
    fn reset(&mut self) {
        self.char_count = 0;
    }

    fn fresh(&mut self, _: ResId) -> TypeVar {
        let ch = (b'a' + self.char_count) as char;
        self.char_count = (self.char_count + 1) % (b'z' - b'a');
        let id = Ident::new(Sym::intern(&format!("'{ch}")), Span::dummy());
        TypeVar::new(id)
    }
}

impl<'ast, 't> TypeChecker<'ast, 't> {
    fn new(
        ctxt: &'t TyCtxt<'t>,
        program: &'ast Program<'ast>,
        res: &'t Resolution<'ast, 't>,
    ) -> Self {
        Self {
            ctxt,
            program,
            res,
            env: Map::default(),
            type_var_src: TypeVarSource::default(),
            skolem: SkolemId::ZERO,
            constraints: Vec::new(),
            subs: Substitution::new(ctxt),
        }
    }

    fn infer(mut self) -> Result<(), InferError<'t>> {
        self.infer_comp_unit(self.program.unit)?;
        self.infer_solve_expr(self.program.main)?;
        Ok(())
    }

    fn type_from_lit(&self, lit: Lit, span: Span) -> Ty<'t> {
        self.ctxt.typ(TyKind::Base(lit.base_type()), span)
    }

    fn constrain(&mut self, lhs: Ty<'t>, rhs: Ty<'t>) {
        //log::trace!("{lhs} ~ {rhs}");
        self.constraints.push(Constraint::equal(lhs, rhs));
    }

    fn fresh_var(&self) -> Ty<'t> {
        self.subs.new_var().1
    }

    /// Generalize a type over its unification variables.
    ///
    /// For example, `generalize('1 -> '1) = 'a -> 'a`.
    fn generalize(&mut self, typ: Ty<'t>) -> Ty<'t> {
        self.type_var_src.reset();
        let typ = self.subs.apply(typ);
        let free_vars = typ.uni_vars();
        if !free_vars.is_empty() {
            for var in free_vars {
                self.subs.insert(
                    var.id,
                    Ty::type_var(self.ctxt, self.type_var_src.fresh(ResId::ZERO /* FIXME */)),
                );
            }
            self.subs.apply(typ)
        } else {
            typ
        }
    }

    fn instantiate(&mut self, typ: Ty<'t>) -> Ty<'t> {
        struct Instantiator<'a> {
            ctxt: &'a TyCtxt<'a>,
            subs: Map<Ident, Ty<'a>>,
        }

        impl<'a> Folder<'a, Ty<'a>> for Instantiator<'a> {
            fn ctxt(&self) -> &'a TyCtxt<'a> {
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
            ctxt: self.ctxt,
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

    fn _skolemize(&mut self, typ: Ty<'t>) -> Ty<'t> {
        struct SkolemReplacer<'a> {
            skolems: Map<TypeVar, Skolem>,
            ctxt: &'a TyCtxt<'a>,
        }

        impl<'a> Folder<'a, Ty<'a>> for SkolemReplacer<'a> {
            fn ctxt(&self) -> &'a TyCtxt<'a> {
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
            ctxt: self.ctxt,
            skolems,
        }
        .fold(typ);
        skolemized
    }

    fn solve_current(&mut self) -> Result<(), InferError<'t>> {
        let constraints: Vec<_> = self.constraints.drain(..).collect();
        let residual = constraint::solve(self, constraints).map_err(InferError::TypeUnifyFail)?;
        if residual.is_empty() {
            Ok(())
        } else {
            Err(InferError::ResidualConstraints(residual))
        }
    }

    fn infer_solve_expr(&mut self, expr: &'ast Expr<'ast>) -> Result<Ty<'t>, InferError<'t>> {
        let res = self.infer_expr(expr)?;
        self.solve_current()?;
        let res = self.generalize(res);
        Ok(res)
    }

    fn infer_comp_unit(&mut self, unit: &'ast CompUnit<'ast>) -> Result<(), InferError<'t>> {
        self.infer_items(unit.items)
    }

    fn infer_items(&mut self, items: &'ast [Sp<Item<'ast>>]) -> Result<(), InferError<'t>> {
        log::trace!("{{");
        log::block_in();
        //FIXME
        // for (&id, value) in &items.values {
        //     let typ = match value.typ {
        //         Some(typ) => {
        //             self.check_expr(value.expr, typ)?;
        //             self.solve_current()?;
        //             typ
        //         }
        //         None => self.infer_solve_expr(value.expr)?,
        //     };
        //     log::trace!("{id} : {typ}");
        //     self.ctxt.set_type(value.path.res().hir_id(), typ);
        // }
        // for (id, mexpr) in &items.modules {
        //     log::trace!("mod {id}");
        //     self.infer_mod_expr(mexpr)?;
        // }
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

    // fn _infer_decl_group(&mut self, _group: TypeDeclGroup<'ast>) -> Result<(), InferError<'t>> {
    //     todo!()
    // }

    fn infer_expr(&mut self, expr: &'ast Expr<'ast>) -> Result<Ty<'t>, InferError<'t>> {
        let typ = match expr.kind {
            // NB. Applications are either function calls (such as `(f a b ...)`)
            //     or "0-arity" applications, i.e., paths.
            ExprKind::Call(..) | ExprKind::Path(_) | ExprKind::Constructor(_) => {
                let (head, args) = match expr.kind {
                    ExprKind::Call(head, args) => (head, args),
                    ExprKind::Path(_) | ExprKind::Constructor(_) => (expr, &[] as &[_]),
                    _ => unreachable!(),
                };
                let head_typ = match head.kind {
                    ExprKind::Path(p) | ExprKind::Constructor(p) => self.infer_path(p),
                    _ => self.infer_expr(head),
                }?;
                let mut typ = self.instantiate(head_typ);
                for arg in args {
                    if let TyKind::Arrow(arg_typ, ret_typ) = *typ.kind() {
                        self.check_expr(arg, arg_typ)?;
                        typ = ret_typ;
                    } else {
                        break;
                    }
                }
                typ
            }
            ExprKind::External(_) => unreachable!(),
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
                //FIXME self.check_expr(expr, typ)?;
                //typ
                todo!()
            }
            ExprKind::Tuple(elems) => {
                let mut typs = Vec::with_capacity(elems.len());
                for elem in elems {
                    typs.push(self.infer_expr(elem)?);
                }
                Ty::tuple(self.ctxt, typs, expr.span)
            }
            ExprKind::Vector(elems) => {
                let base_typ = self.fresh_var();
                for elem in elems {
                    let elem_typ = self.infer_expr(elem)?;
                    self.constrain(base_typ, elem_typ);
                }
                self.ctxt.typ(TyKind::Vector(base_typ), expr.span)
            }
            ExprKind::Seq(e1, e2) => {
                self.check_expr(
                    e1,
                    self.ctxt.typ(TyKind::Base(BaseType::Unit), Span::dummy()),
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
                    self.ctxt.typ(TyKind::Base(BaseType::Bool), Span::dummy()),
                )?;
                let then_typ = self.infer_expr(then_expr)?;
                let else_typ = self.infer_expr(else_expr)?;
                self.constrain(then_typ, else_typ);
                then_typ
            }
        };
        let res = self.res[expr.ast_id];
        self.env.insert(res, typ);
        Ok(typ)
    }

    /// Infer the type of a lambda expression `(\args -> body)`.
    fn infer_lambda(
        &mut self,
        args: &'ast [Pat<'ast>],
        body: &'ast Expr<'ast>,
    ) -> Result<Ty<'t>, InferError<'t>> {
        if let Some((first, rest)) = args.split_first() {
            let arg_typ = self.infer_pat(first)?;
            let ret_typ = self.infer_lambda(rest, body)?;
            Ok(Ty::arrow(self.ctxt, arg_typ, ret_typ))
        } else {
            self.infer_expr(body)
        }
    }

    /// Infer the type of a path by looking it up in the environment.
    fn infer_path(&mut self, path: Path<'ast>) -> Result<Ty<'t>, InferError<'t>> {
        let res = self.res[path.ast_id];
        Ok(match self.env.get(&res) {
            Some(typ) => *typ,
            None => {
                let typ = if let Some(cons) = self.res.constructors.get(&res) {
                    cons.typ
                } else {
                    let value = self
                        .res
                        .values
                        .get(&res)
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
                self.env.insert(res, typ);
                typ
            }
        })
    }

    /// Infer a type for a pattern.
    fn infer_pat(&mut self, pat: &'ast Pat<'ast>) -> Result<Ty<'t>, InferError<'t>> {
        let typ = match pat.kind {
            PatKind::Wild => self.fresh_var(),
            PatKind::Var(id) => {
                let var = self.fresh_var();
                let res = self.res[id.ast_id];
                self.env.insert(res, var);
                var
            }
            PatKind::Lit(l) => self.type_from_lit(l, pat.span),
            PatKind::Ann(pat, typ) => {
                //FIXME self.check_pat(pat, typ)?;
                //typ
                todo!()
            }
            PatKind::Tuple(pats) => Ty::tuple(self.ctxt, self.infer_pats(pats)?, pat.span),
            PatKind::Constructor(cons, args) => {
                // TODO. well-formed check for cons_t
                let cons_typ = self.infer_path(cons)?;
                if args.is_empty() {
                    cons_typ
                } else {
                    let arg_typs = self.infer_pats(args)?;
                    let ret_typ = self.fresh_var();
                    let cons_typ = self.instantiate(cons_typ);
                    self.constrain(Ty::n_arrow(self.ctxt, arg_typs, ret_typ), cons_typ);
                    ret_typ
                }
            }
            PatKind::Or(_pats) => todo!("implement or patterns"),
        };
        let res = self.res[pat.ast_id];
        self.env.insert(res, typ);
        Ok(typ)
    }

    fn infer_pats(&mut self, pats: &'ast [Pat<'ast>]) -> Result<Vec<Ty<'t>>, InferError<'t>> {
        let mut typs = Vec::with_capacity(pats.len());
        for pat in pats {
            typs.push(self.infer_pat(pat)?);
        }
        Ok(typs)
    }

    /// Check an expression against a type.
    fn check_expr(
        &mut self,
        expr: &'ast Expr<'ast>,
        expected: Ty<'t>,
    ) -> Result<(), InferError<'t>> {
        //let expected = self.skolemize(expected);
        match (expr.kind, expected.kind()) {
            (ExprKind::External(_), _) => (),
            (ExprKind::Lit(l), TyKind::Base(b)) if l.base_type() == *b => (),
            (ExprKind::Lit(l), TyKind::Var(_)) => {
                self.constrain(expected, self.type_from_lit(l, expr.span));
            }

            // TODO. these branches probably aren't necessary
            (ExprKind::Lambda(lambda), TyKind::Uni(_)) => {
                let mut arg_typs = Vec::with_capacity(lambda.args.len());
                let ret_typ =
                    self.check_lambda_var(lambda.args, lambda.body, expected, &mut arg_typs)?;
                self.constrain(expected, Ty::n_arrow(self.ctxt, arg_typs, ret_typ));
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
        args: &'ast [Pat<'ast>],
        body: &'ast Expr<'ast>,
        var: Ty<'t>,
        arg_typs: &mut Vec<Ty<'t>>,
    ) -> Result<Ty<'t>, InferError<'t>> {
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
        args: &'ast [Pat<'ast>],
        body: &'ast Expr<'ast>,
        arrow: Ty<'t>,
    ) -> Result<(), InferError<'t>> {
        if let Some((first, rest)) = args.split_first() {
            match *arrow.kind() {
                TyKind::Arrow(arg, ret) => {
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
    fn check_pat(&mut self, pat: &'ast Pat<'ast>, expected: Ty<'t>) -> Result<(), InferError<'t>> {
        match (pat.kind, expected.kind()) {
            (PatKind::Wild, _) => (),
            (PatKind::Var(path), _) => {
                let res = self.res[path.ast_id];
                self.env.insert(res, expected);
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
