use std::{
    borrow::Borrow,
    collections::hash_map::Entry,
    fmt,
    hash::Hash,
    ops::{Index, IndexMut},
};

use base::{
    hash::{Map, Set},
    index::{Idx, IndexVec},
    pp::FormatIterator,
};
use span::{
    Ident, SourceId, Sp, Span, Sym,
    diag::{Diagnostic, Label, Level},
};
use syntax::ast;

use crate::{
    Arena, Constructor, DefKind, HirCtxt, HirId, HirMap, Res, TypeDecl, UniVar, UniVarId, Value,
    Visitor,
    hir::{self, Ty},
};

pub(crate) fn lower_program_in<'ast, 'hir>(
    hir_ctxt: &'hir HirCtxt<'hir>,
    program: &'ast ast::Program<'ast>,
) -> Result<&'hir hir::Program<'hir>, Diagnostic> {
    LoweringContext::new(hir_ctxt)
        .lower_program(program)
        .map_err(Diagnostic::from)
}

enum LowerError {
    Parse(Diagnostic),
    Unbound(Sym, Span),
    Resolve(String, Span),
    DuplicateLocalBinding(Sym, Span, Vec<Span>),
    DuplicateItemBinding(Namespace, Sym, Span, Span),
    RecursiveValue(Sym, Span),
    InvalidInt(Span, std::num::ParseIntError),
}

impl From<LowerError> for Diagnostic {
    fn from(error: LowerError) -> Self {
        match error {
            LowerError::Parse(diag) => diag,
            LowerError::Unbound(sym, span) => Diagnostic::new(Level::Error)
                .with_message(format!("identifier `{sym}` not found in scope"))
                .with_labels(vec![Label::new(span, "undefined")]),
            LowerError::Resolve(path, span) => Diagnostic::new(Level::Error)
                .with_message(format!("cannot resolve `{path}`"))
                .with_labels(vec![Label::new(span, "not found").primary()]),
            LowerError::DuplicateLocalBinding(sym, span, other_spans) => {
                let mut labels =
                    vec![Label::new(span, format!("duplicate binding for `{sym}`")).primary()];
                for span in other_spans {
                    labels.push(Label::new(span, "redefined here"));
                }
                Diagnostic::new(Level::Error)
                    .with_message("duplicate local binding at the same level")
                    .with_labels(labels)
            }
            LowerError::DuplicateItemBinding(ns, sym, span, other_span) => {
                Diagnostic::new(Level::Error)
                    .with_message(format!("duplicate item binding in {ns} namespace"))
                    .with_labels(vec![
                        Label::new(span, format!("duplicate binding for `{sym}`")).primary(),
                        Label::new(other_span, "first defined here"),
                    ])
            }
            LowerError::RecursiveValue(sym, span) => Diagnostic::new(Level::Error)
                .with_message(format!("definition of `{sym}` produces a recursive value"))
                .with_labels(vec![Label::new(span, "")]),
            LowerError::InvalidInt(span, e) => Diagnostic::new(Level::Error)
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
    values: IdentMap<HirId>,
    types: IdentMap<HirId>,
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
    Inline(Ident),
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

struct LoweringContext<'hir> {
    hir_ctxt: &'hir HirCtxt<'hir>,

    values: HirMap<Value<'hir>>,
    constructors: HirMap<Constructor<'hir>>,
    types: HirMap<TypeDecl<'hir>>,

    // Cached imports, associating a source id to an already lowered comp unit.
    imports: Map<SourceId, (ModuleId, &'hir hir::CompUnit<'hir>)>,

    // The graph of modules.
    modules: IndexVec<ModuleId, Module>,

    // Stack of modules we are in.
    module_stack: Vec<ModuleId>,
    local_module_stack: Vec<Ident>,

    // Local bindings introduced by patterns.
    locals: ScopedMap<Ident, hir::Path<'hir>>,

    // Which module (comp unit or inline) we are processing.
    current_module_id: Option<ModuleId>,

    // If we're currently importing std.
    in_std_import: bool,
}

impl<'hir> LoweringContext<'hir> {
    fn new(hir_ctxt: &'hir HirCtxt<'hir>) -> Self {
        Self {
            hir_ctxt,
            imports: Map::default(),
            values: HirMap::default(),
            constructors: HirMap::default(),
            types: HirMap::default(),
            modules: IndexVec::default(),
            module_stack: Vec::new(),
            local_module_stack: Vec::new(),
            locals: ScopedMap::default(),
            current_module_id: None,
            in_std_import: false,
        }
    }

    fn current_module_id(&self) -> ModuleId {
        self.current_module_id.unwrap()
    }

    fn current_module(&self) -> &Module {
        self.modules.get(self.current_module_id()).unwrap()
    }

    fn current_module_mut(&mut self) -> &mut Module {
        let module_id = self.current_module_id();
        self.modules.get_mut(module_id).unwrap()
    }

    fn current_comp_unit(&self) -> SourceId {
        for &module_id in self.module_stack.iter().rev() {
            let module = self.modules.get(module_id).unwrap();
            match module.kind {
                ModuleKind::Inline(_) => (),
                ModuleKind::Unit(source_id) => return source_id,
            }
        }
        unreachable!()
    }

    fn with_module<R>(&mut self, module: ModuleId, f: impl FnOnce(&mut Self) -> R) -> R {
        let old_module = std::mem::replace(&mut self.current_module_id, Some(module));
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

    fn resolve_path(
        &self,
        ns: Namespace,
        path: ast::Path<'_>,
    ) -> Result<hir::Path<'hir>, LowerError> {
        if let Some(id) = path.as_ident() {
            // Attempt to find a pattern binding first.
            if ns == Namespace::Value
                && let Some(&path) = self.locals.get(&id)
            {
                return Ok(path);
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
                    // Don't cross pass compilation unit.
                    break;
                }
                if let Some(hir_id) = module.values.get(&id) {
                    return Ok(self.hir_ctxt.path(
                        path.root,
                        path.access.iter().copied(),
                        path.span(),
                        Res::Def(DefKind::Value, *hir_id),
                    ));
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
                .ok_or(LowerError::Resolve(path.to_string(), path.span()))?;
        }

        if ns == Namespace::Value
            && let Some(hir_id) = curr.values.get(&path.leaf())
        {
            return Ok(self.hir_ctxt.path(
                path.root,
                path.access.iter().copied(),
                path.span(),
                Res::Def(DefKind::Value, *hir_id),
            ));
        }

        if ns == Namespace::Type
            && let Some(hir_id) = curr.types.get(&path.leaf())
        {
            return Ok(self.hir_ctxt.path(
                path.root,
                path.access.iter().copied(),
                path.span(),
                Res::Def(DefKind::Type, *hir_id),
            ));
        }

        Err(LowerError::Resolve(path.to_string(), path.span()))
    }

    fn current_value_path(&mut self, id: Ident) -> hir::Path<'hir> {
        let hir_id = self.hir_ctxt.new_hir_node();
        if let Some((&root, access)) = self.local_module_stack.split_first() {
            log::trace!("{}.{}.{id} -> {hir_id}", root, access.iter().format("."));
            self.hir_ctxt.path(
                root,
                access.into_iter().copied().chain(std::iter::once(id)),
                id.span,
                Res::Def(DefKind::Value, hir_id),
            )
        } else {
            log::trace!("{id} -> {hir_id}");
            self.hir_ctxt
                .path(id, [], id.span, Res::Def(DefKind::Value, hir_id))
        }
    }

    fn std_import_item(
        &mut self,
        seen: &mut Seen,
        items: &mut hir::Items<'hir>,
    ) -> Result<(), LowerError> {
        let arena = syntax::Arena::default();
        match syntax::std_import(&arena) {
            Ok(import_item) => {
                self.in_std_import = true;
                self.lower_item(import_item, seen, items)?;
                self.in_std_import = false;
            }
            Err(diag) => span::diag::emit(diag),
        }
        Ok(())
    }

    fn lower_program<'ast>(
        mut self,
        program: &'ast ast::Program<'ast>,
    ) -> Result<&'hir hir::Program<'hir>, LowerError> {
        let source_id = program.unit.source_id;
        let module = self.modules.push(Module::new(ModuleKind::Unit(source_id)));
        let (unit, main) = self.with_module(module, move |self_| {
            let items = self_.lower_items(true, program.unit.items)?;
            let main = self_.lower_expr(program.main)?;
            let unit = self_
                .hir_ctxt
                .arena
                .alloc(hir::CompUnit { source_id, items });
            Ok((unit, main))
        })?;
        Ok(self.hir_ctxt.arena.alloc(hir::Program {
            unit,
            main,
            imports: self
                .imports
                .iter()
                .map(|(&source_id, &(_, comp_unit))| (source_id, comp_unit))
                .collect(),
            values: self.values,
            constructors: self.constructors,
            types: self.types,
        }))
    }

    fn lower_comp_unit<'ast>(
        &mut self,
        unit: &ast::CompUnit<'ast>,
    ) -> Result<(ModuleId, &'hir hir::CompUnit<'hir>), LowerError> {
        let source_id = unit.source_id;
        let module_id = self.modules.push(Module::new(ModuleKind::Unit(source_id)));
        let items = self.with_module(module_id, |self_| {
            self_.lower_items(!self_.in_std_import, unit.items)
        })?;
        Ok((
            module_id,
            self.hir_ctxt
                .arena
                .alloc(hir::CompUnit { source_id, items }),
        ))
    }

    fn lower_import(
        &mut self,
        id: Ident,
        import_path: &std::path::Path,
    ) -> Result<(ModuleId, SourceId), LowerError> {
        let mut file_path = std::path::PathBuf::new();
        if let Some(base_path) =
            span::with_source_map(|sm| sm[self.current_comp_unit()].path.clone())
        {
            file_path.push(base_path.parent().unwrap());
        }

        file_path.push(import_path);
        Ok(
            if let Some(source_id) =
                span::with_source_map(|sm| sm.lookup_existing_source_id(&file_path))
            {
                self.imports
                    .get(&source_id)
                    .map(|&(module_id, _)| (module_id, source_id))
                    .unwrap()
            } else {
                let ast_arena = syntax::Arena::default();
                let comp_unit = syntax::parse_comp_unit_in(&ast_arena, &file_path)
                    .map_err(LowerError::Parse)?;
                self.local_module_stack.push(id);
                let (module_id, comp_unit) = self.lower_comp_unit(comp_unit)?;
                self.local_module_stack.pop();
                self.imports
                    .insert(comp_unit.source_id, (module_id, comp_unit));
                (module_id, comp_unit.source_id)
            },
        )
    }

    fn lower_items<'ast>(
        &mut self,
        import_std: bool,
        items: &'ast [Sp<ast::Item<'ast>>],
    ) -> Result<&'hir hir::Items<'hir>, LowerError> {
        let mut seen = Seen::default();
        let mut hir_items = hir::Items::default();
        if import_std {
            self.std_import_item(&mut seen, &mut hir_items)?;
        }
        for item in items {
            self.lower_item(item, &mut seen, &mut hir_items)?;
        }
        Ok(self.hir_ctxt.arena.alloc(hir_items))
    }

    fn lower_item<'ast>(
        &mut self,
        item: &'ast Sp<ast::Item<'ast>>,
        seen: &mut Seen,
        items: &mut hir::Items<'hir>,
    ) -> Result<(), LowerError> {
        match **item {
            ast::Item::Type(decls) => {
                self.lower_type_decl_group(decls, seen, items)?;
            }
            ast::Item::Val(id, typ, e) => {
                seen.update(Namespace::Value, id)?;
                let path = self.current_value_path(id);
                let hir_id = path.res().hir_id();

                // Insert hir_id into scope before lowering value
                // to allow recursive functions.
                self.current_module_mut().values.insert(id, hir_id);

                let expr = self.lower_expr(e)?;

                struct RecursiveVisitor {
                    hir_id: HirId,
                    recursive_function: bool,
                    recursive_value: bool,
                }

                impl<'a> Visitor<hir::Expr<'a>> for RecursiveVisitor {
                    fn visit(&mut self, expr: hir::Expr<'a>) {
                        use hir::ExprKind;
                        match expr.kind() {
                            ExprKind::Path(p) if p.res().hir_id() == self.hir_id => {
                                self.recursive_value = true;
                            }
                            ExprKind::App(_, e, args) => {
                                if let ExprKind::Path(p) = e.kind()
                                    && p.res().hir_id() == self.hir_id
                                {
                                    self.recursive_function = true;
                                }
                            }
                            _ => expr.visit_with(self),
                        }
                    }
                }

                let mut recursive_visitor = RecursiveVisitor {
                    hir_id,
                    recursive_function: false,
                    recursive_value: false,
                };
                recursive_visitor.visit(expr);

                // Guard against recursive values, i.e. val x = x
                if recursive_visitor.recursive_value {
                    return Err(LowerError::RecursiveValue(id.sym, id.span));
                }

                let value = Value {
                    path,
                    hir_id,
                    recursive: recursive_visitor.recursive_function,
                    expr,
                    typ: match typ {
                        Some(typ) => Some(self.lower_type(typ)?),
                        None => None,
                    },
                };
                items.values.insert(id, value);
                self.values.insert(hir_id, value);
            }
            ast::Item::External(id, typ, s) => {
                seen.update(Namespace::Value, id)?;
                let path = self.current_value_path(id);
                let hir_id = path.res().hir_id();
                let typ = self.lower_type(typ)?;
                let value = Value {
                    path,
                    hir_id,
                    recursive: false,
                    expr: self
                        .hir_ctxt
                        .expr(hir::ExprKind::External(s.sym, typ), s.span),
                    typ: Some(typ),
                };
                self.current_module_mut().values.insert(id, hir_id);
                items.values.insert(id, value);
                self.values.insert(hir_id, value);
            }
            ast::Item::Mod(id, mexpr) => {
                seen.update(Namespace::Mod, id)?;
                let kind = match **mexpr {
                    ast::ModExpr::Path(p) => todo!(),
                    ast::ModExpr::Struct(items) => {
                        let module_id = self.modules.push(Module::new(ModuleKind::Inline(id)));
                        self.current_module_mut().modules.insert(id, module_id);
                        self.local_module_stack.push(id);
                        let items =
                            self.with_module(module_id, |self_| self_.lower_items(false, items))?;
                        self.local_module_stack.pop();
                        hir::ModExprKind::Struct(items)
                    }
                    ast::ModExpr::Import(path) => {
                        let (module_id, source_id) = self.lower_import(id, path)?;
                        self.current_module_mut().modules.insert(id, module_id);
                        hir::ModExprKind::Import(source_id)
                    }
                };
                let mexpr = self.hir_ctxt.arena.alloc(hir::ModExpr {
                    kind,
                    span: mexpr.span(),
                });
                items.modules.insert(id, mexpr);
            }
        }
        Ok(())
    }

    fn lower_type_decl_group<'ast>(
        &mut self,
        group: &'ast [ast::TypeDecl<'ast>],
        seen: &mut Seen,
        items: &mut hir::Items,
    ) -> Result<hir::TypeDeclGroup<'hir>, LowerError> {
        for decl in group {
            seen.update(Namespace::Type, decl.id)?;
        }

        let mut decls = Vec::with_capacity(group.len());
        for decl in group {
            let hir_id = self.hir_ctxt.new_hir_node();
            self.current_module_mut().types.insert(decl.id, hir_id);
            let decl = self.lower_type_decl(decl, seen)?;
            self.types.insert(hir_id, decl);
            items.types.insert(hir_id);
            decls.push(decl);

            // FIXME
            self.hir_ctxt.set_type(
                hir_id,
                Ty::uni_var(
                    self.hir_ctxt,
                    UniVar::new(UniVarId::from_u32(u32::MAX), hir::Kind::new(0)),
                ),
            );
        }

        Ok(hir::TypeDeclGroup {
            decls: self.hir_ctxt.arena.alloc_from_iter(decls),
        })
    }

    fn lower_type_decl<'ast>(
        &mut self,
        decl: &'ast ast::TypeDecl<'ast>,
        seen: &mut Seen,
    ) -> Result<hir::TypeDecl<'hir>, LowerError> {
        let vars = self
            .hir_ctxt
            .arena
            .alloc_from_iter(decl.vars.iter().map(|&id| hir::TypeVar::new(id)));
        let hir_id = self.hir_ctxt.new_hir_node();

        let kind = match decl.kind {
            ast::TypeDeclKind::Alias(typ) => {
                let typ = self.lower_type(typ)?;
                self.hir_ctxt.set_type(hir_id, typ);
                hir::TypeDeclKind::Alias(typ)
            }
            ast::TypeDeclKind::Variant(variants) => {
                let mut constructors = Set::default();
                let path = self.hir_ctxt.path(
                    decl.id,
                    [],
                    decl.span,
                    Res::Def(hir::DefKind::Type, hir_id),
                );
                let typ = Ty::app(
                    self.hir_ctxt,
                    path,
                    vars.iter().map(|&v| Ty::type_var(self.hir_ctxt, v)),
                    path.span(),
                );
                self.hir_ctxt.set_type(hir_id, typ);
                for &(id, args) in variants {
                    let mut new_args = Vec::with_capacity(args.len());
                    for arg in args {
                        new_args.push(self.lower_type_unscoped(arg)?);
                    }
                    let cons_typ = Ty::n_arrow(self.hir_ctxt, new_args.iter().copied(), typ);
                    seen.update(Namespace::Value, id)?;
                    let cons_hir_id = self.hir_ctxt.new_hir_node();
                    constructors.insert(cons_hir_id);
                    self.current_module_mut().values.insert(id, cons_hir_id);
                    self.constructors.insert(cons_hir_id, Constructor {
                        id,
                        typ: cons_typ,
                        arity: new_args.len(),
                        decl: hir_id,
                    });
                    self.hir_ctxt.set_type(cons_hir_id, cons_typ);
                }
                hir::TypeDeclKind::Variant(self.hir_ctxt.arena.alloc(constructors))
            }
        };

        Ok(hir::TypeDecl {
            id: decl.id,
            vars,
            kind,
            span: decl.span,
        })
    }

    fn lower_type<'ast>(&mut self, typ: &'ast Sp<ast::Type<'ast>>) -> Result<Ty<'hir>, LowerError> {
        self.lower_type_unscoped(typ)
    }

    fn lower_type_unscoped<'ast>(
        &mut self,
        typ: &'ast Sp<ast::Type<'ast>>,
    ) -> Result<Ty<'hir>, LowerError> {
        use hir::{BaseType, TyKind, TypeVar};
        Ok(match &**typ {
            ast::Type::Base(ast::BaseType::Unit) => {
                self.hir_ctxt.typ(TyKind::Base(BaseType::Unit), typ.span())
            }
            ast::Type::Base(ast::BaseType::Bool) => {
                self.hir_ctxt.typ(TyKind::Base(BaseType::Bool), typ.span())
            }
            ast::Type::Base(ast::BaseType::Str) => {
                self.hir_ctxt.typ(TyKind::Base(BaseType::Str), typ.span())
            }
            ast::Type::Base(ast::BaseType::Int32) => {
                self.hir_ctxt.typ(TyKind::Base(BaseType::Int32), typ.span())
            }
            ast::Type::Var(id) => {
                /*
                let id = self
                    .renamer
                    .find_ident(Namespace::Type, *a)
                    .unwrap_or_else(|_| self.renamer.fresh_ident(Namespace::Type, *a));
                    */
                Ty::type_var(self.hir_ctxt, TypeVar::new(*id))
            }
            ast::Type::Arrow(arg, ret) => {
                let arg = self.lower_type_unscoped(arg)?;
                let ret = self.lower_type_unscoped(ret)?;
                Ty::arrow(self.hir_ctxt, hir::NO_WEB, arg, ret)
            }
            ast::Type::Tuple(ts) => {
                let mut elems = Vec::with_capacity(ts.len());
                for t in ts.iter() {
                    elems.push(self.lower_type_unscoped(t)?);
                }
                Ty::tuple(self.hir_ctxt, elems, typ.span())
            }
            ast::Type::Vector(t) => Ty::new(
                self.hir_ctxt,
                TyKind::Vector(self.lower_type_unscoped(t)?),
                typ.span(),
            ),
            ast::Type::Row(_fields, _ext) => todo!("record types"),
            ast::Type::Path(p) => Ty::app(
                self.hir_ctxt,
                self.resolve_path(Namespace::Value, *p)?,
                [],
                typ.span(),
            ),
            ast::Type::App(head, ts) => {
                let head = self.resolve_path(Namespace::Type, *head)?;
                let mut args = Vec::with_capacity(ts.len());
                for t in ts.iter() {
                    args.push(self.lower_type_unscoped(t)?);
                }
                Ty::app(self.hir_ctxt, head, args, typ.span())
            }
        })
    }

    fn lower_pat<'ast>(
        &mut self,
        pat: &'ast Sp<ast::Pat<'ast>>,
    ) -> Result<&'hir hir::Pat<'hir>, LowerError> {
        self.lower_pat_mut(pat)
            .map(|p| &*self.hir_ctxt.arena.alloc(p))
    }

    fn lower_pats<'ast>(
        &mut self,
        pats: &'ast [Sp<ast::Pat<'ast>>],
    ) -> Result<&'hir [hir::Pat<'hir>], LowerError> {
        let mut new_pats = Vec::with_capacity(pats.len());
        for pat in pats {
            new_pats.push(self.lower_pat_mut(pat)?);
        }
        Ok(self.hir_ctxt.arena.alloc_from_iter(new_pats))
    }

    fn lower_pat_mut<'ast>(
        &mut self,
        pat: &'ast Sp<ast::Pat<'ast>>,
    ) -> Result<hir::Pat<'hir>, LowerError> {
        use hir::PatKind;
        let kind = match **pat {
            ast::Pat::Wild => PatKind::Wild,
            ast::Pat::Lit(l) => PatKind::Lit(self.lower_lit(l, pat.span())?),
            ast::Pat::Var(id) => {
                let hir_id = self.hir_ctxt.new_hir_node();
                let path = self.hir_ctxt.path(id, [], id.span, Res::Local(hir_id));
                self.locals.insert(id, path);
                PatKind::Var(path)
            }
            ast::Pat::Ann(p, t) => PatKind::Ann(self.lower_pat(p)?, self.lower_type(t)?),
            ast::Pat::Tuple(ps) => PatKind::Tuple(self.lower_pats(ps)?),
            ast::Pat::Constructor(cons, ps) => PatKind::Constructor(
                self.resolve_path(Namespace::Value, cons)?,
                self.lower_pats(ps)?,
            ),
            ast::Pat::Or(ps) => PatKind::Or(self.lower_pats(ps)?),
        };
        Ok(hir::Pat {
            kind,
            span: pat.span,
        })
    }

    fn lower_lambda<'ast>(
        &mut self,
        lambda: ast::Lambda<'ast>,
    ) -> Result<hir::Lambda<'hir>, LowerError> {
        self.check_duplicates_group(lambda.args)?;
        self.with_local_scope(|self_| {
            let args = self_.lower_pats(lambda.args)?;
            let body = self_.lower_expr(lambda.body)?;
            Ok(hir::Lambda {
                web_id: hir::NO_WEB,
                args,
                body,
            })
        })
    }

    fn lower_expr<'ast>(
        &mut self,
        expr: &'ast Sp<ast::Expr<'ast>>,
    ) -> Result<hir::Expr<'hir>, LowerError> {
        use hir::ExprKind;
        let kind = match **expr {
            ast::Expr::Lit(l) => ExprKind::Lit(self.lower_lit(l, expr.span())?),
            ast::Expr::Path(p) => ExprKind::Path(self.resolve_path(Namespace::Value, p)?),
            ast::Expr::Constructor(p) => {
                ExprKind::Constructor(self.resolve_path(Namespace::Value, p)?)
            }
            ast::Expr::Lambda(l) => ExprKind::Lambda(self.lower_lambda(l)?),
            ast::Expr::Let(binds, body) => {
                let mut new_binds = Vec::with_capacity(binds.len());
                let body = self.with_local_scope(|self_| {
                    for bind in binds.iter() {
                        self_.check_duplicates_one(&bind.0)?;
                        let p = self_.lower_pat_mut(&bind.0)?;
                        let e = self_.lower_expr(&bind.1)?;
                        new_binds.push((p, e));
                    }
                    self_.lower_expr(body)
                })?;
                ExprKind::Let(self.hir_ctxt.arena.alloc_from_iter(new_binds), body)
            }
            ast::Expr::Case(e, arms) => {
                let e = self.lower_expr(e)?;
                let mut new_arms = Vec::with_capacity(arms.len());
                for arm in arms.iter() {
                    self.check_duplicates_one(&arm.0)?;
                    new_arms.push(self.with_local_scope(|self_| {
                        let p = self_.lower_pat_mut(&arm.0)?;
                        let e = self_.lower_expr(&arm.1)?;
                        Ok((p, e))
                    })?);
                }
                ExprKind::Case(e, self.hir_ctxt.arena.alloc_from_iter(new_arms))
            }
            ast::Expr::If(cond, e1, e2) => {
                let cond = self.lower_expr(cond)?;
                let e1 = self.with_local_scope(|self_| self_.lower_expr(e1))?;
                let e2 = self.with_local_scope(|self_| self_.lower_expr(e2))?;
                ExprKind::If(cond, e1, e2)
            }
            ast::Expr::Ann(e, t) => ExprKind::Ann(self.lower_expr(e)?, self.lower_type(t)?),
            ast::Expr::App(head, es) => {
                let head = self.lower_expr(head)?;
                let mut args = Vec::with_capacity(es.len());
                for e in es.iter() {
                    args.push(self.lower_expr_arg(e)?);
                }
                ExprKind::App(hir::NO_WEB, head, self.hir_ctxt.arena.alloc_from_iter(args))
            }
            ast::Expr::Tuple(es) => {
                let mut elems = Vec::with_capacity(es.len());
                for e in es.iter() {
                    elems.push(self.lower_expr(e)?);
                }
                ExprKind::Tuple(self.hir_ctxt.arena.alloc_from_iter(elems))
            }
            ast::Expr::Vector(es) => {
                let mut elems = Vec::with_capacity(es.len());
                for e in es.iter() {
                    elems.push(self.lower_expr(e)?);
                }
                ExprKind::Vector(self.hir_ctxt.arena.alloc_from_iter(elems))
            }
            ast::Expr::Seq(e1, e2) => {
                let e1 = self.lower_expr(e1)?;
                let e2 = self.lower_expr(e2)?;
                ExprKind::Seq(e1, e2)
            }
        };
        Ok(self.hir_ctxt.expr(kind, expr.span))
    }

    fn lower_expr_arg<'ast>(
        &mut self,
        expr_arg: &'ast Sp<ast::ExprArg<'ast>>,
    ) -> Result<hir::ExprArg<'hir>, LowerError> {
        Ok(match &**expr_arg {
            ast::ExprArg::Expr(e) => hir::ExprArg::Expr(self.lower_expr(e)?),
            ast::ExprArg::Type(t) => hir::ExprArg::Type(self.lower_type(t)?),
        })
    }

    fn lower_lit(&self, lit: ast::Lit, span: Span) -> Result<hir::Lit, LowerError> {
        Ok(match lit {
            ast::Lit::Unit => hir::Lit::Unit,
            ast::Lit::Bool(b) => hir::Lit::Bool(b),
            ast::Lit::Str(s) => hir::Lit::Str(s),
            ast::Lit::Int32(n) => {
                #[allow(clippy::from_str_radix_10)]
                let n = i32::from_str_radix(&n.as_str().replace("_", ""), 10)
                    .map_err(|e| LowerError::InvalidInt(span, e))?;
                hir::Lit::Int32(n)
            }
        })
    }
}

#[derive(Default)]
struct Duplicates {
    // Map symbols to (first occurence, rebindings).
    bindings: Map<Sym, (Span, Vec<Span>)>,
}

impl Duplicates {
    fn check(self) -> Result<(), LowerError> {
        for (sym, redefined) in self.bindings {
            if !redefined.1.is_empty() {
                return Err(LowerError::DuplicateLocalBinding(
                    sym,
                    redefined.0,
                    redefined.1,
                ));
            }
        }
        Ok(())
    }
}

fn visit_with<'ast, V>(pat: Sp<ast::Pat<'ast>>, v: &mut V)
where
    V: Visitor<Sp<ast::Pat<'ast>>>,
{
    use ast::Pat;
    match *pat {
        Pat::Ann(p, _) => v.visit(*p),
        Pat::Constructor(_, ps) | Pat::Tuple(ps) | Pat::Or(ps) => {
            ps.iter().for_each(|&p| v.visit(p))
        }
        Pat::Wild | Pat::Var(_) | Pat::Lit(_) => (),
    }
}

impl<'ast> Visitor<Sp<ast::Pat<'ast>>> for Duplicates {
    fn visit(&mut self, pat: Sp<ast::Pat<'ast>>) {
        if let ast::Pat::Var(id) = *pat {
            self.bindings
                .entry(id.sym)
                .and_modify(|e| e.1.push(id.span))
                .or_insert((id.span, Vec::new()));
        }
        visit_with(pat, self);
    }
}

impl LoweringContext<'_> {
    fn check_duplicates_one<'ast>(&self, pat: &'ast Sp<ast::Pat<'ast>>) -> Result<(), LowerError> {
        let mut dups = Duplicates::default();
        dups.visit(*pat);
        dups.check()
    }

    fn check_duplicates_group<'ast>(
        &self,
        pats: &'ast [Sp<ast::Pat<'ast>>],
    ) -> Result<(), LowerError> {
        let mut dups = Duplicates::default();
        for pat in pats {
            dups.visit(*pat);
        }
        dups.check()
    }
}

#[derive(Default)]
struct Seen {
    spans: PerNs<Map<Sym, Span>>,
}

impl Seen {
    fn update(&mut self, ns: Namespace, id: Ident) -> Result<(), LowerError> {
        if let Some(span) = self.spans[ns].get(&id.sym) {
            return Err(LowerError::DuplicateItemBinding(ns, id.sym, id.span, *span));
        }
        self.spans[ns].insert(id.sym, id.span);
        Ok(())
    }
}
