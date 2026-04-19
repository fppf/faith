use std::{
    borrow::Borrow,
    collections::hash_map::Entry,
    fmt,
    hash::Hash,
    ops::{Index, IndexMut},
};

use base::{
    hash::{IndexMap, Map},
    index::IndexVec,
};
use span::{
    Ident, SourceId, Sp, Span, Sym,
    diag::{Diagnostic, Label, Level},
};
use syntax::ast::{
    self, AstVisitor, CompUnit, Expr, ExprKind, Item, Lit, ModExpr, Pat, PatKind, Path, Program,
    Type, TypeDeclKind,
};

use crate::{
    DefKind, Res,
    hir::{self, HirVisitor, Var},
    ty::{Adt, Constructor, Ty, TyCtxt, TyKind, TypeVar},
};

pub fn resolve_program_in<'ast, 't>(
    ctxt: &'t TyCtxt<'t>,
    program: &'ast Program<'ast>,
) -> Result<hir::Program<'t>, Diagnostic> {
    Resolver::new(ctxt, program)
        .resolve()
        .map_err(Diagnostic::from)
}

#[derive(Debug)]
enum ResolveError {
    Resolve(String, Span),
    DuplicateLocalBinding(Sym, Span, Vec<Span>),
    DuplicateItemBinding(Namespace, Sym, Span, Span),
    RecursiveValue(Sym, Span),
    InvalidInt(Span, std::num::ParseIntError),
}

impl From<ResolveError> for Diagnostic {
    fn from(error: ResolveError) -> Self {
        match error {
            ResolveError::Resolve(path, span) => Diagnostic::new(Level::Error)
                .with_message(format!("cannot resolve `{path}`"))
                .with_labels(vec![Label::new(span, "not found").primary()]),
            ResolveError::DuplicateLocalBinding(sym, span, other_spans) => {
                let mut labels =
                    vec![Label::new(span, format!("duplicate binding for `{sym}`")).primary()];
                for span in other_spans {
                    labels.push(Label::new(span, "redefined here"));
                }
                Diagnostic::new(Level::Error)
                    .with_message("duplicate local binding at the same level")
                    .with_labels(labels)
            }
            ResolveError::DuplicateItemBinding(ns, sym, span, other_span) => {
                Diagnostic::new(Level::Error)
                    .with_message(format!("duplicate item binding in {ns} namespace"))
                    .with_labels(vec![
                        Label::new(span, format!("duplicate binding for `{sym}`")).primary(),
                        Label::new(other_span, "first defined here"),
                    ])
            }
            ResolveError::RecursiveValue(sym, span) => Diagnostic::new(Level::Error)
                .with_message(format!("definition of `{sym}` produces a recursive value"))
                .with_labels(vec![Label::new(span, "")]),
            ResolveError::InvalidInt(span, e) => Diagnostic::new(Level::Error)
                .with_message("parsed integer is invalid")
                .with_labels(vec![Label::new(span, e.to_string())]),
        }
    }
}

base::newtype_index! {
    struct ModuleId {}
}

#[derive(Debug)]
struct Module {
    kind: ModuleKind,
    values: Map<Ident, Res>,
    cons: Map<Ident, Res>,
    types: Map<Ident, Res>,
    children: Map<Ident, ModuleId>,
}

impl Module {
    fn new(kind: ModuleKind) -> Self {
        Self {
            kind,
            values: Map::default(),
            cons: Map::default(),
            types: Map::default(),
            children: Map::default(),
        }
    }

    fn get_res(&self, ns: Namespace, id: Ident) -> Option<Res> {
        match ns {
            Namespace::Value => self.values.get(&id).copied(),
            Namespace::Cons => self.cons.get(&id).copied(),
            Namespace::Type => self.types.get(&id).copied(),
            Namespace::Mod => None,
        }
    }
}

#[derive(Debug)]
enum ModuleKind {
    Inline,
    Unit(SourceId),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Namespace {
    Value,
    Cons,
    Type,
    Mod,
}

impl fmt::Display for Namespace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Namespace::Value => "value",
            Namespace::Cons => "cons",
            Namespace::Type => "type",
            Namespace::Mod => "module",
        }
        .fmt(f)
    }
}

#[derive(Clone, Copy, Default, Debug)]
struct PerNs<T> {
    value_ns: T,
    cons_ns: T,
    type_ns: T,
    mod_ns: T,
}

impl<T> Index<Namespace> for PerNs<T> {
    type Output = T;

    fn index(&self, ns: Namespace) -> &Self::Output {
        match ns {
            Namespace::Value => &self.value_ns,
            Namespace::Cons => &self.cons_ns,
            Namespace::Type => &self.type_ns,
            Namespace::Mod => &self.mod_ns,
        }
    }
}

impl<T> IndexMut<Namespace> for PerNs<T> {
    fn index_mut(&mut self, ns: Namespace) -> &mut Self::Output {
        match ns {
            Namespace::Value => &mut self.value_ns,
            Namespace::Cons => &mut self.cons_ns,
            Namespace::Type => &mut self.type_ns,
            Namespace::Mod => &mut self.mod_ns,
        }
    }
}

// A map with scoped values. Taken from `gluon/base/src/scoped_map.rs`.
struct ScopedMap<K, V> {
    // Key to stack of values.
    map: Map<K, Vec<V>>,
    // None is used as a marker to delimit scopes.
    scopes: Vec<Option<K>>,
}

impl<K, V> Default for ScopedMap<K, V> {
    fn default() -> Self {
        Self {
            map: Map::default(),
            scopes: Vec::new(),
        }
    }
}

impl<K: Eq + Hash + Clone, V> ScopedMap<K, V> {
    fn enter_scope(&mut self) {
        self.scopes.push(None);
    }

    fn exit_scope(&mut self) {
        while let Some(Some(k)) = self.scopes.pop() {
            self.map.get_mut(&k).map(|v| v.pop());
        }
    }

    #[inline]
    fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.map.get(k).and_then(|v| v.last())
    }

    #[inline]
    fn insert(&mut self, k: K, v: V) {
        match self.map.entry(k.clone()) {
            Entry::Vacant(e) => e.insert(Vec::new()),
            Entry::Occupied(e) => e.into_mut(),
        }
        .push(v);
        self.scopes.push(Some(k));
    }
}

struct Resolver<'ast, 't> {
    ctxt: &'t TyCtxt<'t>,
    program: &'ast Program<'ast>,

    // The graph of modules.
    modules: IndexVec<ModuleId, Module>,
    imports: Map<SourceId, ModuleId>,
    units: Vec<hir::CompUnit<'t>>,

    // Stack of modules we are in.
    module_stack: Vec<ModuleId>,

    // Local bindings introduced by patterns.
    locals: ScopedMap<Ident, Var<'t>>,

    variables: Map<Res, Var<'t>>,

    // Which module (comp unit or inline) we are processing.
    current_module_id: ModuleId,
}

impl<'ast, 't> Resolver<'ast, 't> {
    fn new(ctxt: &'t TyCtxt<'t>, program: &'ast Program<'ast>) -> Self {
        let mut modules = IndexVec::default();
        let current_module_id = modules.push(Module::new(ModuleKind::Unit(program.unit.source_id)));
        Self {
            ctxt,
            program,
            modules,
            imports: Map::default(),
            units: Vec::with_capacity(program.imports.len()),
            module_stack: Vec::new(),
            locals: ScopedMap::default(),
            variables: Map::default(),
            current_module_id,
        }
    }

    fn resolve(mut self) -> Result<hir::Program<'t>, ResolveError> {
        let (items, main) = self.with_module(self.current_module_id, |self_| {
            let items = self_.resolve_items(self.program.unit.items)?;
            let main = self_.resolve_expr(self.program.main)?;
            Ok((items, main))
        })?;

        let this_unit = hir::CompUnit {
            source_id: self.program.unit.source_id,
            items,
        };

        let mut imports = Map::default();
        for unit in self.units {
            imports.insert(unit.source_id, unit);
        }

        Ok(hir::Program {
            imports,
            unit: this_unit,
            main,
        })
    }

    fn make_var(&mut self, id: ast::Id, res: Res, typ: Option<Ty<'t>>) -> Var<'t> {
        let mut var = Var::new(id.ident, res, id.ident.span);
        var.typ = typ;
        self.variables.insert(res, var);
        var
    }

    fn make_external_var(&mut self, id: ast::Id, res: Res, typ: Ty<'t>, sym: Sym) -> Var<'t> {
        let mut var = Var::new(id.ident, res, id.ident.span);
        var.external = Some(sym);
        var.typ = Some(typ);
        self.variables.insert(res, var);
        var
    }

    fn make_local(&mut self, id: ast::Id) -> Var<'t> {
        let res = Res::Local(self.ctxt.new_res_id());
        let var = self.make_var(id, res, None);
        self.locals.insert(id.ident, var);
        var
    }

    fn current_module(&self) -> &Module {
        &self.modules[self.current_module_id]
    }

    fn current_module_mut(&mut self) -> &mut Module {
        &mut self.modules[self.current_module_id]
    }

    #[allow(unused)]
    fn current_comp_unit(&self) -> SourceId {
        for &module_id in self.module_stack.iter().rev() {
            let module = self.modules.get(module_id).unwrap();
            match module.kind {
                ModuleKind::Inline => (),
                ModuleKind::Unit(source_id) => return source_id,
            }
        }
        unreachable!()
    }

    fn with_module<R>(&mut self, module: ModuleId, f: impl FnOnce(&mut Self) -> R) -> R {
        let old_module = std::mem::replace(&mut self.current_module_id, module);
        self.module_stack.push(module);
        let ret = f(self);
        self.module_stack.pop();
        self.current_module_id = old_module;
        ret
    }

    fn with_local_scope<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.locals.enter_scope();
        let ret = f(self);
        self.locals.exit_scope();
        ret
    }

    fn resolve_path(&mut self, ns: Namespace, path: Path<'ast>) -> Result<Var<'t>, ResolveError> {
        // TODO. cache already resolved paths.

        let res = self.resolve_path_inner(ns, path)?;
        log::trace!("resolve_path {path} => {res}");
        Ok(res)
    }

    fn resolve_path_inner(&self, ns: Namespace, path: Path<'ast>) -> Result<Var<'t>, ResolveError> {
        if let Some(id) = path.as_ident() {
            // Attempt to find a pattern binding first.
            if ns == Namespace::Value
                && let Some(&var) = self.locals.get(&id.ident)
            {
                return Ok(var);
            }

            // Traverse the current module stack outwards,
            // finding the closest binding.
            //
            // This allows us to reference items defined in an
            // enclosing (inline) module scope. For example,
            //
            //   mod m = {
            //      val x = 0
            //      mod n = {
            //         val y = x
            //      }
            //   }
            //
            for &module_id in self.module_stack.iter().rev() {
                let module = &self.modules[module_id];
                if let ModuleKind::Unit(_) = module.kind {
                    // Don't cross pass compilation unit boundary.
                    break;
                }
                if let Some(res) = module.get_res(ns, id.ident) {
                    return Ok(self.variables[&res]);
                }
            }
        }

        // Descend into the innermost module in the path prefix.
        let mut module = self.current_module();
        for segment in path.segments().take(path.access.len()) {
            module = module
                .children
                .get(&segment)
                .and_then(|&module_id| self.modules.get(module_id))
                .ok_or(ResolveError::Resolve(path.to_string(), path.span()))?;
            log::trace!("    descend into {:?}", module);
        }

        module
            .get_res(ns, path.leaf())
            .and_then(|res| self.variables.get(&res).copied())
            .ok_or_else(|| ResolveError::Resolve(path.to_string(), path.span()))
    }

    fn resolve_comp_unit(&mut self, unit: &'ast CompUnit<'ast>) -> Result<ModuleId, ResolveError> {
        let module_id = self
            .modules
            .push(Module::new(ModuleKind::Unit(unit.source_id)));
        let items = self.with_module(module_id, |self_| self_.resolve_items(unit.items))?;
        let unit = hir::CompUnit {
            source_id: unit.source_id,
            items,
        };
        self.units.push(unit);
        Ok(module_id)
    }

    fn resolve_import(
        &mut self,
        _id: Ident,
        source_id: SourceId,
    ) -> Result<ModuleId, ResolveError> {
        if let Some(&module_id) = self.imports.get(&source_id) {
            Ok(module_id)
        } else {
            log::trace!("resolve {:?}", source_id);
            let comp_unit = self.program.imports[&source_id];
            let module_id = self.resolve_comp_unit(comp_unit)?;
            assert!(self.imports.insert(source_id, module_id).is_none());
            Ok(module_id)
        }
    }

    fn resolve_items(
        &mut self,
        items: &'ast [Sp<Item<'ast>>],
    ) -> Result<Vec<hir::Item<'t>>, ResolveError> {
        let mut new_items = Vec::with_capacity(items.len());
        let mut seen = Seen::default();
        for item in items {
            new_items.extend(self.resolve_item(item, &mut seen)?);
        }
        Ok(new_items)
    }

    // Resolve an AST item to zero or more HIR items.
    //
    // Inline modules may produce items which will be flattened into
    // the result.
    //
    // Some AST items (e.g. type decls) will not produce HIR items,
    // and instead become metadata on the type context.
    fn resolve_item(
        &mut self,
        item: &'ast Sp<Item<'ast>>,
        seen: &mut Seen,
    ) -> Result<Vec<hir::Item<'t>>, ResolveError> {
        match item.value {
            Item::Type(decls) => {
                log::trace!("[resolve_item] Item::Type");
                // To permit recursive type decls, we must first register all
                // decls within the decl list.
                let mut decl_vars = Vec::with_capacity(decls.len());
                for decl in decls {
                    seen.update(Namespace::Type, decl.id.ident)?;

                    let decl_res = Res::Def(DefKind::Type, self.ctxt.new_res_id());
                    let decl_typ = Ty::new(self.ctxt, TyKind::User(decl.id.ident, decl_res));
                    let decl_var = self.make_var(decl.id, decl_res, Some(decl_typ));
                    decl_vars.push(decl_var);

                    self.current_module_mut()
                        .types
                        .insert(decl.id.ident, decl_res);

                    log::trace!("  {} => {decl_res}", decl.id);
                }

                for (decl, decl_var) in decls.iter().zip(decl_vars) {
                    match decl.kind {
                        TypeDeclKind::Alias(ast_ty) => {
                            let _ty = self.lower_type(ast_ty)?;
                            todo!("fix alias implementation")
                        }
                        TypeDeclKind::Variant(variants) => {
                            // A variant (ADT)
                            //
                            //   type T 'a1 .. 'ak =
                            //      | C1 t11 t12 ..
                            //      ..
                            //      | Cn tn1 tn2 ..
                            let adt_res = decl_var.res;

                            // Construct (T 'a1 .. 'ak)
                            let adt_typ = Ty::app(
                                self.ctxt,
                                decl_var.typ.unwrap(),
                                decl.vars
                                    .iter()
                                    .map(|id| Ty::type_var(self.ctxt, TypeVar::new(id.ident))),
                            );

                            let mut constructors = IndexMap::default();
                            for (index, &(id, args)) in variants.iter().enumerate() {
                                seen.update(Namespace::Value, id.ident)?;

                                let cons_res = Res::Def(DefKind::Cons, self.ctxt.new_res_id());

                                self.current_module_mut().cons.insert(id.ident, cons_res);

                                let mut new_args = Vec::with_capacity(args.len());
                                for arg in args {
                                    new_args.push(self.lower_type_unscoped(arg)?);
                                }

                                // Constructor (Ci ti1 .. tik) is given type
                                // (ti1 -> .. -> tik -> (T 'a1 .. 'ak))
                                let arity = new_args.len();
                                let cons_typ =
                                    Ty::n_arrow(self.ctxt, new_args.iter().copied(), adt_typ);
                                let cons_var = self.make_var(id, cons_res, Some(cons_typ));
                                let cons = Constructor {
                                    var: cons_var,
                                    args: self.ctxt.arena.alloc_from_iter(new_args),
                                    index,
                                    arity,
                                    adt: adt_res,
                                };
                                constructors.insert(cons_res, cons);

                                log::trace!("    {id} => {cons_res}");
                            }

                            let adt = Adt {
                                id: decl.id.ident,
                                constructors,
                            };
                            self.ctxt.add_adt(adt_res, adt);
                        }
                    }
                }
            }
            Item::External(id, ast_ty, mapped_to) => {
                let ident = id.ident;
                seen.update(Namespace::Value, ident)?;

                let typ = self.lower_type(ast_ty)?;

                let ext_res = Res::Def(DefKind::Value, self.ctxt.new_res_id());
                let _ext_var = self.make_external_var(id, ext_res, typ, mapped_to.sym);

                self.current_module_mut().values.insert(ident, ext_res);
            }
            Item::Value(id, ast_ty, expr) => {
                let (ident, ast_id) = (id.ident, id.ast_id);
                seen.update(Namespace::Value, ident)?;

                let val_res = Res::Def(DefKind::Value, self.ctxt.new_res_id());
                let val_var = self.make_var(id, val_res, None);

                // Insert res into scope before resolving expr
                // to allow for recursive functions.
                self.current_module_mut().values.insert(ident, val_res);

                let mut new_expr = self.resolve_expr(expr)?;

                struct RecursiveVisitor {
                    res: Res,
                    recursive_function: bool,
                    recursive_value: bool,
                }

                impl<'t> HirVisitor<'t> for RecursiveVisitor {
                    fn visit_expr(&mut self, expr: &mut hir::Expr<'t>) {
                        match &mut expr.kind {
                            hir::ExprKind::Var(v) => {
                                self.recursive_value = v.res == self.res;
                            }
                            hir::ExprKind::Call(f, args) => {
                                if let hir::ExprKind::Var(v) = f.kind {
                                    self.recursive_function = v.res == self.res;
                                }
                                for arg in args {
                                    self.visit_expr(arg);
                                }
                            }
                            _ => expr.visit_with(self),
                        }
                    }
                }

                let mut recursive_visitor = RecursiveVisitor {
                    res: val_res,
                    recursive_function: false,
                    recursive_value: false,
                };
                recursive_visitor.visit_expr(&mut new_expr);

                // Guard against recursive values, i.e. val x = x
                if recursive_visitor.recursive_value {
                    return Err(ResolveError::RecursiveValue(ident.sym, ident.span));
                }

                let recursive = recursive_visitor.recursive_function;
                let expected_typ = if let Some(ty) = ast_ty {
                    Some(Sp::new(self.lower_type(ty)?, ty.span()))
                } else {
                    None
                };

                log::trace!("{ident} {} => {}", ast_id, val_res);
                return Ok(vec![hir::Item::Expr {
                    var: val_var,
                    recursive,
                    expr: new_expr,
                    expected_typ,
                    typ: None,
                }]);
            }
            Item::Mod(id, mexpr) => {
                seen.update(Namespace::Mod, id.ident)?;
                match mexpr.value {
                    ModExpr::Path(_p) => todo!("implement module aliases"),
                    ModExpr::Struct(items) => {
                        let module_id = self.modules.push(Module::new(ModuleKind::Inline));
                        self.current_module_mut()
                            .children
                            .insert(id.ident, module_id);
                        let new_items =
                            self.with_module(module_id, |self_| self_.resolve_items(items))?;
                        return Ok(new_items);
                    }
                    ModExpr::Import(path) => {
                        let module_id = self.resolve_import(id.ident, path)?;
                        self.current_module_mut()
                            .children
                            .insert(id.ident, module_id);
                    }
                }
            }
        }
        Ok(Vec::new())
    }

    fn lower_type(&mut self, typ: &'ast Sp<Type<'ast>>) -> Result<Ty<'t>, ResolveError> {
        self.lower_type_unscoped(typ)
    }

    fn lower_type_unscoped(&mut self, typ: &'ast Sp<Type<'ast>>) -> Result<Ty<'t>, ResolveError> {
        let ty = match typ.value {
            Type::Base(b) => Ty::new(self.ctxt, TyKind::Base(b)),
            Type::Var(id) => {
                // FIXME
                Ty::type_var(self.ctxt, TypeVar::new(id.ident))
            }
            Type::Arrow(arg, ret) => {
                let arg = self.lower_type_unscoped(arg)?;
                let ret = self.lower_type_unscoped(ret)?;
                Ty::arrow(self.ctxt, arg, ret)
            }
            Type::Tuple(ts) => {
                let mut elems = Vec::with_capacity(ts.len());
                for t in ts.iter() {
                    elems.push(self.lower_type_unscoped(t)?);
                }
                Ty::tuple(self.ctxt, elems)
            }
            Type::Vector(t) => {
                let t = self.lower_type_unscoped(t)?;
                Ty::new(self.ctxt, TyKind::Vector(t))
            }
            Type::App(head, ts) => {
                let decl_var = self.resolve_path_inner(Namespace::Type, head)?;
                let head = Ty::new(self.ctxt, TyKind::User(decl_var.id, decl_var.res));
                let mut args = Vec::with_capacity(ts.len());
                for t in ts.iter() {
                    args.push(self.lower_type_unscoped(t)?);
                }
                Ty::app(self.ctxt, head, args)
            }
            Type::Row(..) => todo!("implement record types"),
        };
        Ok(ty)
    }

    fn resolve_pat(&mut self, pat: &'ast Pat<'ast>) -> Result<hir::Pat<'t>, ResolveError> {
        let kind = match pat.kind {
            PatKind::Wild => hir::PatKind::Wild,
            PatKind::Lit(l) => hir::PatKind::Lit(wf_lit(l, pat.span)?),
            PatKind::Var(id) => hir::PatKind::Var(self.make_local(id)),
            PatKind::Ann(p, t) => {
                let p = self.resolve_pat(p)?;
                let ty = self.lower_type(t)?;
                hir::PatKind::Ann(Box::new(p), Sp::new(ty, t.span))
            }
            PatKind::Tuple(ps) => hir::PatKind::Tuple(self.resolve_pats(ps)?),
            PatKind::Cons(cons, ps) => {
                let var = self.resolve_path(Namespace::Cons, cons)?;
                hir::PatKind::Cons(var, self.resolve_pats(ps)?)
            }
            PatKind::Or(ps) => hir::PatKind::Or(self.resolve_pats(ps)?),
        };
        Ok(hir::Pat::new(kind, pat.span))
    }

    fn resolve_pats(&mut self, pats: &'ast [Pat<'ast>]) -> Result<Vec<hir::Pat<'t>>, ResolveError> {
        let mut new_pats = Vec::with_capacity(pats.len());
        for pat in pats {
            new_pats.push(self.resolve_pat(pat)?);
        }
        Ok(new_pats)
    }

    fn resolve_expr(&mut self, expr: &'ast Expr<'ast>) -> Result<hir::Expr<'t>, ResolveError> {
        let kind = match expr.kind {
            ExprKind::Lit(l) => hir::ExprKind::Lit(wf_lit(l, expr.span)?),
            ExprKind::Path(p) => {
                let var = self.resolve_path(Namespace::Value, p)?;
                hir::ExprKind::Var(var)
            }
            ExprKind::Cons(p) => {
                let var = self.resolve_path(Namespace::Cons, p)?;
                hir::ExprKind::Var(var)
            }
            ExprKind::Lambda(l) => {
                self.check_duplicates_many(l.args)?;
                self.with_local_scope(|self_| {
                    let args = self_.resolve_pats(l.args)?;
                    let body = self_.resolve_expr(l.body)?;
                    Ok(hir::ExprKind::Lambda(hir::Lambda {
                        args,
                        body: Box::new(body),
                    }))
                })?
            }
            ExprKind::Let(binds, body) => self.with_local_scope(|self_| {
                let mut new_binds = Vec::with_capacity(binds.len());
                for bind in binds.iter() {
                    self_.check_duplicates(&bind.0)?;
                    let pat = self_.resolve_pat(&bind.0)?;
                    let expr = self_.resolve_expr(&bind.1)?;
                    new_binds.push((pat, expr));
                }
                let new_body = self_.resolve_expr(body)?;
                Ok(hir::ExprKind::Let(new_binds, Box::new(new_body)))
            })?,
            ExprKind::Case(e, arms) => {
                let new_e = self.resolve_expr(e)?;
                let mut new_arms = Vec::with_capacity(arms.len());
                for arm in arms.iter() {
                    self.check_duplicates(&arm.0)?;
                    self.with_local_scope(|self_| {
                        let pat = self_.resolve_pat(&arm.0)?;
                        let expr = self_.resolve_expr(&arm.1)?;
                        new_arms.push((pat, expr));
                        Ok(())
                    })?;
                }
                hir::ExprKind::Case(Box::new(new_e), new_arms, None)
            }
            ExprKind::If(cond, e1, e2) => {
                let new_cond = self.resolve_expr(cond)?;
                let new_e1 = self.with_local_scope(|self_| self_.resolve_expr(e1))?;
                let new_e2 = self.with_local_scope(|self_| self_.resolve_expr(e2))?;
                hir::ExprKind::If(Box::new(new_cond), Box::new(new_e1), Box::new(new_e2))
            }
            ExprKind::Ann(e, t) => {
                let new_e = self.resolve_expr(e)?;
                let ty = self.lower_type(t)?;
                hir::ExprKind::Ann(Box::new(new_e), Sp::new(ty, t.span))
            }
            ExprKind::Call(head, args) => {
                let new_head = self.resolve_expr(head)?;
                let new_args = self.resolve_exprs(args)?;
                hir::ExprKind::Call(Box::new(new_head), new_args)
            }
            ExprKind::Tuple(es) => {
                let new_es = self.resolve_exprs(es)?;
                hir::ExprKind::Tuple(new_es)
            }
            ExprKind::Vector(es) => {
                let new_es = self.resolve_exprs(es)?;
                hir::ExprKind::Vector(new_es)
            }
            ExprKind::Seq(e1, e2) => {
                let new_e1 = self.resolve_expr(e1)?;
                let new_e2 = self.resolve_expr(e2)?;
                hir::ExprKind::Seq(Box::new(new_e1), Box::new(new_e2))
            }
        };
        Ok(hir::Expr::new(kind, expr.span))
    }

    fn resolve_exprs(
        &mut self,
        exprs: &'ast [Expr<'ast>],
    ) -> Result<Vec<hir::Expr<'t>>, ResolveError> {
        let mut new_exprs = Vec::with_capacity(exprs.len());
        for expr in exprs {
            new_exprs.push(self.resolve_expr(expr)?);
        }
        Ok(new_exprs)
    }
}

fn wf_lit(lit: Lit, span: Span) -> Result<Lit, ResolveError> {
    if let Lit::Int32(n) = lit {
        #[allow(clippy::from_str_radix_10)]
        if let Err(e) = i32::from_str_radix(&n.as_str().replace("_", ""), 10) {
            return Err(ResolveError::InvalidInt(span, e));
        }
    }
    Ok(lit)
}

#[derive(Default)]
struct Duplicates {
    // Map symbols to (first occurence, rebindings).
    bindings: Map<Sym, (Span, Vec<Span>)>,
}

impl Duplicates {
    fn check(self) -> Result<(), ResolveError> {
        for (sym, redefined) in self.bindings {
            if !redefined.1.is_empty() {
                return Err(ResolveError::DuplicateLocalBinding(
                    sym,
                    redefined.0,
                    redefined.1,
                ));
            }
        }
        Ok(())
    }
}

impl<'ast> AstVisitor<'ast> for Duplicates {
    fn visit_pat(&mut self, pat: &'ast Pat<'ast>) {
        if let PatKind::Var(id) = pat.kind {
            let id = id.ident;
            self.bindings
                .entry(id.sym)
                .and_modify(|e| e.1.push(id.span))
                .or_insert((id.span, Vec::new()));
        }
        pat.visit_with(self);
    }
}

impl<'ast> Resolver<'ast, '_> {
    fn check_duplicates(&self, pat: &'ast Pat<'ast>) -> Result<(), ResolveError> {
        let mut dups = Duplicates::default();
        dups.visit_pat(pat);
        dups.check()
    }

    fn check_duplicates_many(&self, pats: &'ast [Pat<'ast>]) -> Result<(), ResolveError> {
        let mut dups = Duplicates::default();
        for pat in pats {
            dups.visit_pat(pat);
        }
        dups.check()
    }
}

#[derive(Default)]
struct Seen {
    spans: PerNs<Map<Sym, Span>>,
}

impl Seen {
    fn update(&mut self, ns: Namespace, id: Ident) -> Result<(), ResolveError> {
        if let Some(span) = self.spans[ns].get(&id.sym) {
            return Err(ResolveError::DuplicateItemBinding(
                ns, id.sym, id.span, *span,
            ));
        }
        self.spans[ns].insert(id.sym, id.span);
        Ok(())
    }
}
