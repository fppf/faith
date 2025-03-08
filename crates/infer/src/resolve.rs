use std::{
    borrow::Borrow,
    collections::hash_map::Entry,
    fmt,
    hash::Hash,
    ops::{Index, IndexMut},
};

use base::{hash::Map, index::IndexVec};
use span::{
    Ident, SourceId, Sp, Span, Sym,
    diag::{Diagnostic, Label, Level},
};
use syntax::ast::{
    AstId, AstVisitor, CompUnit, Expr, ExprKind, Item, Lit, ModExpr, Pat, PatKind, Path, Program,
    Type, TypeDecl, TypeDeclKind,
};

use crate::{
    TyCtxt,
    typ::{Ty, TyKind, TypeVar},
};

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

pub fn resolve_program_in<'ast, 't>(
    ctxt: &'t TyCtxt<'t>,
    program: &'ast Program<'ast>,
) -> Result<Resolution<'ast, 't>, Diagnostic> {
    Resolver::new(ctxt, program)
        .resolve()
        .map_err(Diagnostic::from)
}

pub struct Resolution<'ast, 't> {
    pub res: Map<AstId, Res>,
    pub last_res_id: ResId,
    pub values: Map<Res, Value<'ast, 't>>,
    pub constructors: Map<Res, Constructor<'t>>,
    pub types: Map<Res, Ty<'t>>,
}

impl<'ast, 't> Index<AstId> for Resolution<'ast, 't> {
    type Output = Res;

    fn index(&self, ast_id: AstId) -> &Self::Output {
        &self.res[&ast_id]
    }
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

type IdentMap<T> = Map<Ident, T>;

base::newtype_index! {
    struct ModuleId {}
}

#[derive(Debug)]
struct Module {
    kind: ModuleKind,
    values: IdentMap<ResId>,
    types: IdentMap<ResId>,
    modules: IdentMap<ModuleId>,
}

impl Module {
    fn new(kind: ModuleKind) -> Self {
        Self {
            kind,
            values: IdentMap::default(),
            types: IdentMap::default(),
            modules: IdentMap::default(),
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
    Type,
    Mod,
}

impl fmt::Display for Namespace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Namespace::Value => "value",
            Namespace::Type => "type",
            Namespace::Mod => "module",
        }
        .fmt(f)
    }
}

#[derive(Clone, Copy, Default, Debug)]
struct PerNs<T> {
    value_ns: T,
    type_ns: T,
    mod_ns: T,
}

impl<T> Index<Namespace> for PerNs<T> {
    type Output = T;

    fn index(&self, ns: Namespace) -> &Self::Output {
        match ns {
            Namespace::Value => &self.value_ns,
            Namespace::Type => &self.type_ns,
            Namespace::Mod => &self.mod_ns,
        }
    }
}

impl<T> IndexMut<Namespace> for PerNs<T> {
    fn index_mut(&mut self, ns: Namespace) -> &mut Self::Output {
        match ns {
            Namespace::Value => &mut self.value_ns,
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

#[derive(Clone, Copy, Debug)]
pub struct Value<'ast, 't> {
    pub recursive: bool,
    pub typ: Option<Ty<'t>>,
    pub expr: &'ast Expr<'ast>,
}

#[derive(Clone, Copy, Debug)]
pub struct Constructor<'t> {
    pub id: Ident,
    pub typ: Ty<'t>,
    pub arity: usize,
    pub decl: Res,
}

struct Resolver<'ast, 't> {
    ctxt: &'t TyCtxt<'t>,
    program: &'ast Program<'ast>,

    res: Resolution<'ast, 't>,

    // The graph of modules.
    modules: IndexVec<ModuleId, Module>,
    imports: Map<SourceId, ModuleId>,

    // Stack of modules we are in.
    module_stack: Vec<ModuleId>,
    local_module_stack: Vec<Ident>,

    // Local bindings introduced by patterns.
    locals: ScopedMap<Ident, Res>,

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
            res: Resolution {
                res: Map::default(),
                last_res_id: ResId::ZERO,
                values: Map::default(),
                constructors: Map::default(),
                types: Map::default(),
            },
            modules,
            imports: Map::default(),
            module_stack: Vec::new(),
            local_module_stack: Vec::new(),
            locals: ScopedMap::default(),
            current_module_id,
        }
    }

    fn resolve(mut self) -> Result<Resolution<'ast, 't>, ResolveError> {
        self.with_module(self.current_module_id, |self_| {
            self_.resolve_items(self.program.unit.items)?;
            self_.resolve_expr(self.program.main)
        })?;
        Ok(self.res)
    }

    fn new_res_id(&mut self) -> ResId {
        let next = self.res.last_res_id + 1;
        self.res.last_res_id = next;
        next
    }

    fn current_module(&self) -> &Module {
        self.modules.get(self.current_module_id).unwrap()
    }

    fn current_module_mut(&mut self) -> &mut Module {
        self.modules.get_mut(self.current_module_id).unwrap()
    }

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

    fn resolve_path(&mut self, ns: Namespace, path: Path<'ast>) -> Result<Res, ResolveError> {
        // If already resolved, reuse.
        if let Some(&res) = self.res.res.get(&path.ast_id) {
            return Ok(res);
        }

        let res = self.resolve_path_inner(ns, path)?;
        self.res.res.insert(path.ast_id, res);
        Ok(res)
    }

    fn resolve_path_inner(&self, ns: Namespace, path: Path<'ast>) -> Result<Res, ResolveError> {
        if let Some(id) = path.as_ident() {
            // Attempt to find a pattern binding first.
            if ns == Namespace::Value
                && let Some(&res) = self.locals.get(&id.ident)
            {
                return Ok(res);
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
                if let Some(&res_id) = module.values.get(&id.ident) {
                    return Ok(Res::Def(DefKind::Value, res_id));
                }
            }
        }

        // Descend into the innermost module in the path prefix.
        let mut curr = self.current_module();
        for segment in path.segments().take(path.access.len()) {
            curr = curr
                .modules
                .get(&segment)
                .and_then(|&module_id| self.modules.get(module_id))
                .ok_or(ResolveError::Resolve(path.to_string(), path.span()))?;
        }

        if ns == Namespace::Value
            && let Some(&res_id) = curr.values.get(&path.leaf())
        {
            return Ok(Res::Def(DefKind::Value, res_id));
        }

        if ns == Namespace::Type
            && let Some(&res_id) = curr.types.get(&path.leaf())
        {
            return Ok(Res::Def(DefKind::Type, res_id));
        }

        Err(ResolveError::Resolve(path.to_string(), path.span()))
    }

    fn resolve_comp_unit(&mut self, unit: &'ast CompUnit<'ast>) -> Result<ModuleId, ResolveError> {
        let source_id = unit.source_id;
        let module_id = self.modules.push(Module::new(ModuleKind::Unit(source_id)));
        self.with_module(module_id, |self_| self_.resolve_items(unit.items))?;
        Ok(module_id)
    }

    fn resolve_import(&mut self, id: Ident, source_id: SourceId) -> Result<ModuleId, ResolveError> {
        if let Some(&module_id) = self.imports.get(&source_id) {
            Ok(module_id)
        } else {
            self.local_module_stack.push(id);
            log::trace!("resolve {:?}", source_id);
            let comp_unit = self.program.imports[&source_id];
            let module_id = self.resolve_comp_unit(comp_unit)?;
            self.local_module_stack.pop();
            assert!(self.imports.insert(source_id, module_id).is_none());
            Ok(module_id)
        }
    }

    fn resolve_items(&mut self, items: &'ast [Sp<Item<'ast>>]) -> Result<(), ResolveError> {
        let mut seen = Seen::default();
        for item in items {
            self.resolve_item(item, &mut seen)?;
        }
        Ok(())
    }

    fn resolve_item(
        &mut self,
        item: &'ast Sp<Item<'ast>>,
        seen: &mut Seen,
    ) -> Result<(), ResolveError> {
        match item.value {
            Item::Type(decls) => {
                self.resolve_type_decl_group(decls, seen)?;
            }
            Item::Value(id, typ, expr) => {
                let (ident, ast_id) = (id.ident, id.ast_id);
                seen.update(Namespace::Value, ident)?;
                let res_id = self.new_res_id();
                let res = Res::Def(DefKind::Value, res_id);
                self.res.res.insert(ast_id, res);

                // Insert hir_id into scope before resolving expr
                // to allow for recursive functions.
                self.current_module_mut().values.insert(ident, res_id);

                self.resolve_expr(expr)?;
                let value = if let ExprKind::External(_) = expr.kind {
                    Value {
                        recursive: false,
                        typ: None, // FIXME
                        expr,
                    }
                } else {
                    struct RecursiveVisitor<'a, 'ast, 't> {
                        resolver: &'a mut Resolver<'ast, 't>,
                        res_id: ResId,
                        recursive_function: bool,
                        recursive_value: bool,
                    }

                    impl<'ast, 't> AstVisitor<'ast> for RecursiveVisitor<'_, 'ast, 't> {
                        fn visit_expr(&mut self, expr: &'ast Expr<'ast>) {
                            match expr.kind {
                                ExprKind::Path(p) => {
                                    let res =
                                        self.resolver.resolve_path(Namespace::Value, p).unwrap();
                                    self.recursive_value = res.res_id() == self.res_id;
                                }
                                ExprKind::Call(e, _) => {
                                    if let ExprKind::Path(p) = e.kind {
                                        let res = self
                                            .resolver
                                            .resolve_path(Namespace::Value, p)
                                            .unwrap();
                                        self.recursive_function = res.res_id() == self.res_id;
                                    }
                                }
                                _ => expr.visit_with(self),
                            }
                        }
                    }

                    let mut recursive_visitor = RecursiveVisitor {
                        resolver: self,
                        res_id,
                        recursive_function: false,
                        recursive_value: false,
                    };
                    recursive_visitor.visit_expr(expr);

                    // Guard against recursive values, i.e. val x = x
                    if recursive_visitor.recursive_value {
                        return Err(ResolveError::RecursiveValue(ident.sym, ident.span));
                    }

                    Value {
                        recursive: recursive_visitor.recursive_function,
                        expr,
                        typ: None, // FIXME
                    }
                };
                self.res.values.insert(res, value);
            }
            Item::Mod(id, mexpr) => {
                seen.update(Namespace::Mod, id.ident)?;
                match mexpr.value {
                    ModExpr::Path(_p) => todo!(),
                    ModExpr::Struct(items) => {
                        let module_id = self.modules.push(Module::new(ModuleKind::Inline));
                        self.current_module_mut()
                            .modules
                            .insert(id.ident, module_id);
                        self.local_module_stack.push(id.ident);
                        self.with_module(module_id, |self_| self_.resolve_items(items))?;
                        self.local_module_stack.pop();
                    }
                    ModExpr::Import(path) => {
                        let module_id = self.resolve_import(id.ident, path)?;
                        self.current_module_mut()
                            .modules
                            .insert(id.ident, module_id);
                    }
                }
            }
        }
        Ok(())
    }

    fn resolve_type_decl_group(
        &mut self,
        group: &'ast [TypeDecl<'ast>],
        seen: &mut Seen,
    ) -> Result<(), ResolveError> {
        // Update seen before resolving decls to allow recursive decls.
        for decl in group {
            seen.update(Namespace::Type, decl.id.ident)?;
        }
        for decl in group {
            self.resolve_type_decl(decl, seen)?;
        }
        Ok(())
    }

    fn resolve_type_decl(
        &mut self,
        decl: &'ast TypeDecl<'ast>,
        seen: &mut Seen,
    ) -> Result<(), ResolveError> {
        let vars = self
            .ctxt
            .arena
            .alloc_from_iter(decl.vars.iter().map(|&id| TypeVar::new(id.ident)));
        let res_id = self.new_res_id();
        let res = Res::Def(DefKind::Type, res_id);

        match decl.kind {
            TypeDeclKind::Alias(typ) => {
                let typ = self.lower_type(typ)?;
                //FIXME self.ctxt.set_type(res_id, typ);
            }
            TypeDeclKind::Variant(variants) => {
                let typ = Ty::app(
                    self.ctxt,
                    res,
                    vars.iter().map(|&v| Ty::type_var(self.ctxt, v)),
                    decl.span,
                );
                //FIXME self.ctxt.set_type(res_id, typ);
                // let mut constructors = Set::default();
                // for &(id, args) in variants {
                //     let mut new_args = Vec::with_capacity(args.len());
                //     for arg in args {
                //         new_args.push(self.lower_type_unscoped(arg)?);
                //     }
                //     let cons_typ = Ty::n_arrow(self.ctxt, new_args.iter().copied(), typ);
                //     seen.update(Namespace::Value, id.ident)?;
                //     let cons_res_id = self.ctxt.new_res_id();
                //     constructors.insert(cons_res_id);
                //     self.current_module_mut()
                //         .values
                //         .insert(id.ident, cons_res_id);
                //     self.constructors.insert(
                //         cons_res_id,
                //         Constructor {
                //             id: id.ident,
                //             typ: cons_typ,
                //             arity: new_args.len(),
                //             decl: res_id,
                //         },
                //     );
                //     //FIXME self.ctxt.set_type(cons_res_id, cons_typ);
                // }
            }
        }
        Ok(())
    }

    fn lower_type(&mut self, typ: &'ast Sp<Type<'ast>>) -> Result<Ty<'t>, ResolveError> {
        self.lower_type_unscoped(typ)
    }

    fn lower_type_unscoped(&mut self, typ: &'ast Sp<Type<'ast>>) -> Result<Ty<'t>, ResolveError> {
        let ty = match typ.value {
            Type::Base(b) => Ty::new(self.ctxt, TyKind::Base(b), typ.span()),
            Type::Var(id) => {
                /*
                let id = self
                    .renamer
                    .find_ident(Namespace::Type, *a)
                    .unwrap_or_else(|_| self.renamer.fresh_ident(Namespace::Type, *a));
                    */
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
                Ty::tuple(self.ctxt, elems, typ.span())
            }
            Type::Vector(t) => {
                let t = self.lower_type_unscoped(t)?;
                Ty::new(self.ctxt, TyKind::Vector(t), typ.span())
            }
            Type::App(head, ts) => {
                let res = self.resolve_path(Namespace::Type, head)?;
                let mut args = Vec::with_capacity(ts.len());
                for t in ts.iter() {
                    args.push(self.lower_type_unscoped(t)?);
                }
                Ty::app(self.ctxt, res, args, typ.span())
            }
            Type::Row(..) => todo!("record types"),
        };
        Ok(ty)
    }

    fn resolve_pat(&mut self, pat: &'ast Pat<'ast>) -> Result<(), ResolveError> {
        match pat.kind {
            PatKind::Wild => Ok(()),
            PatKind::Lit(l) => wf_lit(l, pat.span),
            PatKind::Var(id) => {
                let res_id = self.new_res_id();
                self.locals.insert(id.ident, Res::Local(res_id));
                Ok(())
            }
            PatKind::Ann(p, _t) => self.resolve_pat(p),
            PatKind::Tuple(ps) => self.resolve_pats(ps),
            PatKind::Constructor(cons, ps) => {
                self.resolve_path(Namespace::Value, cons)?;
                self.resolve_pats(ps)
            }
            PatKind::Or(ps) => self.resolve_pats(ps),
        }
    }

    fn resolve_pats(&mut self, pats: &'ast [Pat<'ast>]) -> Result<(), ResolveError> {
        for pat in pats {
            self.resolve_pat(pat)?;
        }
        Ok(())
    }

    fn resolve_expr(&mut self, expr: &'ast Expr<'ast>) -> Result<(), ResolveError> {
        match expr.kind {
            ExprKind::External(_) => Ok(()),
            ExprKind::Lit(l) => wf_lit(l, expr.span),
            ExprKind::Path(p) | ExprKind::Constructor(p) => {
                let _ = self.resolve_path(Namespace::Value, p)?;
                Ok(())
            }
            ExprKind::Lambda(l) => {
                self.check_duplicates_group(l.args)?;
                self.with_local_scope(|self_| {
                    self_.resolve_pats(l.args)?;
                    self_.resolve_expr(l.body)
                })
            }
            ExprKind::Let(binds, body) => self.with_local_scope(|self_| {
                for bind in binds.iter() {
                    self_.check_duplicates_one(&bind.0)?;
                    self_.resolve_pat(&bind.0)?;
                    self_.resolve_expr(&bind.1)?;
                }
                self_.resolve_expr(body)
            }),
            ExprKind::Case(e, arms) => {
                self.resolve_expr(e)?;
                for arm in arms.iter() {
                    self.check_duplicates_one(&arm.0)?;
                    self.with_local_scope(|self_| {
                        self_.resolve_pat(&arm.0)?;
                        self_.resolve_expr(&arm.1)
                    })?;
                }
                Ok(())
            }
            ExprKind::If(cond, e1, e2) => {
                self.resolve_expr(cond)?;
                self.with_local_scope(|self_| self_.resolve_expr(e1))?;
                self.with_local_scope(|self_| self_.resolve_expr(e2))
            }
            ExprKind::Ann(e, _t) => self.resolve_expr(e),
            ExprKind::Call(head, es) => {
                self.resolve_expr(head)?;
                for e in es.iter() {
                    self.resolve_expr(e)?;
                }
                Ok(())
            }
            ExprKind::Tuple(es) | ExprKind::Vector(es) => {
                for e in es.iter() {
                    self.resolve_expr(e)?;
                }
                Ok(())
            }
            ExprKind::Seq(e1, e2) => {
                self.resolve_expr(e1)?;
                self.resolve_expr(e2)
            }
        }
    }
}

fn wf_lit(lit: Lit, span: Span) -> Result<(), ResolveError> {
    match lit {
        Lit::Int32(n) =>
        {
            #[allow(clippy::from_str_radix_10)]
            if let Err(e) = i32::from_str_radix(&n.as_str().replace("_", ""), 10) {
                return Err(ResolveError::InvalidInt(span, e));
            }
        }
        _ => (),
    }
    Ok(())
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
    fn check_duplicates_one(&self, pat: &'ast Pat<'ast>) -> Result<(), ResolveError> {
        let mut dups = Duplicates::default();
        dups.visit_pat(pat);
        dups.check()
    }

    fn check_duplicates_group(&self, pats: &'ast [Pat<'ast>]) -> Result<(), ResolveError> {
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
