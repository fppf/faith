use hash::Map;
use hir::*;
use span::{SourceId, Span, Sym};

use crate::error::InferError;

// `Environment` is the main data structure during type inference for resolving names to their
// respective information.
//
// ## Compilation units
// When we finish typechecking a comp unit, we will cache the comp unit's module type in the
// `comp_units` map. Then whenever we encounter another reference to the compilation unit, we can
// retrieve the cached module type. For example, a module import `mod m = import "xyz"` will
// first try to determine if `"xyz"` refers to a compilation unit we already parsed/typechecked. If
// so, we reuse the result, otherwise we load and typecheck the file referred to by `"xyz"`.
pub struct Environment<'hir> {
    pub comp_units: Map<SourceId, &'hir ModType<'hir>>,

    scopes: Vec<Scope<'hir>>,
    arena: &'hir Arena<'hir>,
}

struct Scope<'hir> {
    kind: ScopeKind,
    values: Map<Ident, Ty<'hir>>,
    types: Map<Ident, TypeDecl<'hir>>,
    constructors: Map<Sym, (usize, Ty<'hir>)>,
    mod_types: Map<Ident, &'hir ModType<'hir>>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ScopeKind {
    Local,
    Module(Ident),
    File(SourceId),
}

impl<'hir> Scope<'hir> {
    fn new(kind: ScopeKind) -> Self {
        Self {
            kind,
            values: Map::default(),
            types: Map::default(),
            constructors: Map::default(),
            mod_types: Map::default(),
        }
    }

    fn as_mod_type(&self, arena: &'hir Arena<'hir>) -> &'hir ModType<'hir> {
        // TODO. this is wrong!!!!
        let ScopeKind::File(source_id) = self.kind else {
            unreachable!()
        };

        let mut specs = Vec::new();

        for (&id, &typ) in self.values.iter() {
            specs.push(Spec {
                kind: SpecKind::Val(id, typ),
                span: Span::dummy(),
            });
        }

        let self_ref = Ident::new(
            Sym::from_str(&source_id.as_raw().to_string()),
            0,
            Span::dummy(),
        );

        arena.alloc(ModType {
            kind: ModTypeKind::Sig(self_ref, arena.alloc_from_iter(specs)),
            span: Span::dummy(),
        })
    }

    fn lookup_constructor(&self, path: Path<'hir>) -> Option<(usize, Ty<'hir>)> {
        if let Some(id) = path.as_ident() {
            return self.constructors.get(&id.sym).copied();
        }

        let mut mtyp = *self.mod_types.get(&path.id())?;
        let depth = path.access_len() - 1;
        'e: for (i, sym) in path.access().enumerate() {
            if let ModTypeKind::Sig(_, sig) = mtyp.kind {
                for spec in sig {
                    match spec.kind {
                        SpecKind::Mod(id, m) if i < depth && id.sym == sym => {
                            mtyp = m;
                            continue 'e;
                        }
                        SpecKind::Type(_, hir::TypeDecl { kind, .. }) if i == depth => {
                            if let TypeDeclKind::Variant(variant) = kind {
                                return variant.constructors.get(&sym).copied();
                            }
                        }
                        _ => (),
                    }
                }
                break 'e;
            } else {
                break 'e;
            }
        }
        None
    }

    fn lookup_value(&self, path: Path<'hir>) -> Option<(Ident, Ty<'hir>)> {
        // TODO. lookup_* are kinda atrocious.
        if let Some(id) = path.as_ident() {
            return self.values.get(&id).map(|&typ| (id, typ));
        }

        let mut mtyp = *self.mod_types.get(&path.id())?;
        let depth = path.access_len() - 1;
        'e: for (i, sym) in path.access().enumerate() {
            if let ModTypeKind::Sig(_, sig) = mtyp.kind {
                for spec in sig {
                    match spec.kind {
                        SpecKind::Mod(id, m) if i < depth && id.sym == sym => {
                            mtyp = m;
                            continue 'e;
                        }
                        SpecKind::Val(id, typ) if i == depth && id.sym == sym => {
                            return Some((id, typ));
                        }
                        _ => (),
                    }
                }
                break 'e;
            } else {
                break 'e;
            }
        }
        None
    }

    fn lookup_type(&self, path: Path<'hir>) -> Option<(Ident, TypeDecl<'hir>)> {
        if let Some(id) = path.as_ident() {
            return self.types.get(&id).map(|&decl| (id, decl));
        }

        let mut mtyp = *self.mod_types.get(&path.id())?;
        let depth = path.access_len() - 1;
        'e: for (i, sym) in path.access().enumerate() {
            if let ModTypeKind::Sig(_, sig) = mtyp.kind {
                for spec in sig {
                    match spec.kind {
                        SpecKind::Mod(id, m) if i < depth && id.sym == sym => {
                            mtyp = m;
                            continue 'e;
                        }
                        SpecKind::Type(id, decl) if i == depth && id.sym == sym => {
                            return Some((id, decl));
                        }
                        SpecKind::TypeGroup(_) => unreachable!(),
                        _ => (),
                    }
                }
                break 'e;
            } else {
                break 'e;
            }
        }
        None
    }
}

impl<'hir> Environment<'hir> {
    pub fn new(arena: &'hir Arena<'hir>) -> Self {
        Self {
            comp_units: Map::default(),
            scopes: Vec::new(),
            arena,
        }
    }

    fn nearest_scope(&self) -> &Scope<'hir> {
        self.scopes.last().unwrap()
    }

    fn nearest_scope_mut(&mut self) -> &mut Scope<'hir> {
        self.scopes.last_mut().unwrap()
    }

    fn _nearest_module_scope(&self) -> &Scope<'hir> {
        for scope in self.scopes.iter().rev() {
            if matches!(scope.kind, ScopeKind::Module(_) | ScopeKind::File(_)) {
                return scope;
            }
        }
        unreachable!()
    }

    fn nearest_module_scope_mut(&mut self) -> &mut Scope<'hir> {
        for scope in self.scopes.iter_mut().rev() {
            if matches!(scope.kind, ScopeKind::Module(_) | ScopeKind::File(_)) {
                return scope;
            }
        }
        unreachable!()
    }

    pub fn insert_value(&mut self, id: Ident, typ: Ty<'hir>) {
        log::trace!("insert_value {id} := {typ}");
        self.nearest_scope_mut().values.insert(id, typ);
    }

    pub fn insert_type_decl(&mut self, id: Option<Ident>, decl: TypeDecl<'hir>) {
        let id = id.unwrap_or(decl.id);

        match decl.kind {
            TypeDeclKind::Variant(variant) => {
                self.nearest_scope_mut()
                    .constructors
                    .extend(variant.constructors.iter());
            }
            TypeDeclKind::Alias(typ) => {
                log::trace!("insert_type_decl {id} := {typ}");
                self.nearest_module_scope_mut().types.insert(id, decl);
            }
        }
    }

    pub fn insert_mod_type(&mut self, id: Ident, mtyp: &'hir ModType<'hir>) {
        self.nearest_module_scope_mut().mod_types.insert(id, mtyp);
    }

    pub fn resolve_use_item(
        &mut self,
        id: Ident,
        path: Path<'hir>,
    ) -> Result<(), InferError<'hir>> {
        if let Ok((_, typ)) = self.lookup_value(path) {
            self.insert_value(id, typ);
            Ok(())
        } else if let Ok(decl) = self.lookup_type_decl(path) {
            self.insert_type_decl(Some(id), decl);
            Ok(())
        } else {
            Err(InferError::ResolveFail(path))
        }
    }

    pub fn lookup_value(&self, path: Path<'hir>) -> Result<(Ident, Ty<'hir>), InferError<'hir>> {
        for scope in self.scopes.iter().rev() {
            if let Some(res) = scope.lookup_value(path) {
                return Ok(res);
            }
        }
        Err(InferError::ResolveFail(path))
    }

    fn lookup_type_decl(&self, path: Path<'hir>) -> Result<TypeDecl<'hir>, InferError<'hir>> {
        for scope in self.scopes.iter().rev() {
            if let Some((_, res)) = scope.lookup_type(path) {
                return Ok(res);
            }
        }
        Err(InferError::ResolveFail(path))
    }

    pub fn lookup_type(&self, path: Path<'hir>) -> Result<Ty<'hir>, InferError<'hir>> {
        self.lookup_type_decl(path).map(|decl| match decl.kind {
            TypeDeclKind::Alias(typ) => typ,
            TypeDeclKind::Variant(_) => Ty::path(self.arena, path),
        })
    }

    pub fn lookup_mod_type(
        &self,
        path: Path<'hir>,
    ) -> Result<&'hir ModType<'hir>, InferError<'hir>> {
        Err(InferError::ResolveFail(path))
    }

    pub fn enter_scope(&mut self, kind: ScopeKind) {
        log::trace!("enter_scope {kind:?}");
        self.scopes.push(Scope::new(kind));
    }

    pub fn exit_scope(&mut self) {
        log::trace!("exit_scope");
        let scope = self.nearest_scope();
        if let ScopeKind::File(source_id) = scope.kind {
            let mtyp = scope.as_mod_type(self.arena);
            self.comp_units.insert(source_id, mtyp);
        }
        self.scopes.pop().unwrap();
    }
}
