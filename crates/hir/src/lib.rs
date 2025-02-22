#![feature(let_chains)]
#![allow(unused)]

mod lower;
mod path;
mod pretty;
mod typ;

use std::{
    cell::{Cell, OnceCell, RefCell},
    fmt,
};

use base::{
    hash::{IndexMap, Map, Set},
    index::{Idx, IndexVec},
};

use span::{Ident, SourceId, Sp, Span, Sym, diag::Diagnostic};

pub use path::*;
pub use typ::*;

#[derive(Default)]
pub struct HirCtxt<'hir> {
    pub arena: Arena<'hir>,
    hir_nodes: RefCell<IndexVec<HirId, HirNode<'hir>>>,
}

#[derive(Default)]
struct HirNode<'hir> {
    typ: OnceCell<Ty<'hir>>,
}

impl<'hir> HirCtxt<'hir> {
    pub fn new_hir_node(&self) -> HirId {
        let mut nodes = self.hir_nodes.borrow_mut();
        nodes.push(HirNode::default())
    }

    pub fn is_ctxt_typed(&self) -> bool {
        self.hir_nodes.borrow().iter_enumerated().all(|(id, node)| {
            if node.typ.get().is_none() {
                println!("{id} -> ???");
                false
            } else {
                true
            }
        })
    }

    pub fn get_type(&self, hir_id: HirId) -> Option<Ty<'hir>> {
        self.hir_nodes
            .borrow()
            .get(hir_id)
            .and_then(|node| node.typ.get())
            .copied()
    }

    pub fn set_type(&self, hir_id: HirId, typ: Ty<'hir>) {
        let mut nodes = self.hir_nodes.borrow_mut();
        let mut node = nodes.get_mut(hir_id).unwrap();
        node.typ.set(typ);
    }
}

pub fn parse_and_lower_program_in<'hir>(
    hir_ctxt: &'hir HirCtxt<'hir>,
    path: &std::path::Path,
) -> Result<&'hir Program<'hir>, Diagnostic> {
    let ast_arena = syntax::Arena::default();
    let ast = syntax::parse_program_in(&ast_arena, path)?;
    lower::lower_program_in(hir_ctxt, ast)
}

pub fn parse_and_lower_str_program_in<'hir>(
    hir_ctxt: &'hir HirCtxt<'hir>,
    src: &str,
) -> Result<&'hir Program<'hir>, Diagnostic> {
    let ast_arena = syntax::Arena::default();
    let ast = syntax::parse_str_program_in(&ast_arena, src)?;
    lower::lower_program_in(hir_ctxt, ast)
}

base::declare_arena!('hir, [
    set: HirSet,
    items: Items<'hir>,
    program: Program<'hir>,
]);

impl<'hir> HirCtxt<'hir> {
    #[inline]
    pub fn path<I>(&'hir self, id: Ident, access: I, span: Span, res: Res) -> Path<'hir>
    where
        I: IntoIterator<Item = Ident>,
    {
        Path::new(
            &self.arena,
            id,
            self.arena.alloc_from_iter(access),
            span,
            res,
        )
    }

    #[inline]
    pub fn typ(&'hir self, kind: TyKind<'hir>, span: Span) -> Ty<'hir> {
        Ty::new(self, kind, span)
    }

    #[inline]
    pub fn expr(&'hir self, kind: ExprKind<'hir>, span: Span) -> Expr<'hir> {
        let hir_id = self.new_hir_node();
        Expr {
            hir_id,
            kind,
            span,
            private: private::HirCtxtOnlyZst,
        }
    }

    #[inline]
    pub fn expr_alloc(&'hir self, kind: ExprKind<'hir>, span: Span) -> &'hir Expr<'hir> {
        self.arena.alloc(self.expr(kind, span))
    }

    #[inline]
    pub fn pat(&'hir self, kind: PatKind<'hir>, span: Span) -> Pat<'hir> {
        let hir_id = self.new_hir_node();
        Pat {
            hir_id,
            kind,
            span,
            private: private::HirCtxtOnlyZst,
        }
    }
}

// TODO. hide creation methods?
base::newtype_index! {
    pub struct HirId {}
}

impl fmt::Display for HirId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.index())
    }
}

pub type HirMap<T> = IndexMap<HirId, T>;
pub type HirSet = Set<HirId>;

base::newtype_index! {
    pub struct WebId {}
}

pub const NO_WEB: WebId = WebId::ZERO;

mod private {
    /// Used to mark things which should only be created via HirCtxt.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub struct HirCtxtOnlyZst;
}

#[derive(Clone, Debug)]
pub struct Program<'hir> {
    pub imports: Map<SourceId, &'hir CompUnit<'hir>>,
    pub values: HirMap<Value<'hir>>,
    pub constructors: HirMap<Constructor<'hir>>,
    pub types: HirMap<TypeDecl<'hir>>,
    pub unit: &'hir CompUnit<'hir>,
    pub main: &'hir Expr<'hir>,
}

#[derive(Clone, Copy, Debug)]
pub struct CompUnit<'hir> {
    pub source_id: SourceId,
    pub items: &'hir Items<'hir>,
}

#[derive(Clone, Copy, Debug)]
pub struct Value<'hir> {
    pub path: Path<'hir>,
    pub hir_id: HirId,
    pub expr: &'hir Expr<'hir>,
    pub recursive: bool,
    pub typ: Option<Ty<'hir>>,
}

#[derive(Clone, Copy, Debug)]
pub struct Constructor<'hir> {
    pub id: Ident,
    pub typ: Ty<'hir>,
    pub arity: usize,
    pub decl: HirId,
}

#[derive(Clone, Copy, Debug)]
pub struct TypeDecl<'hir> {
    pub id: Ident,
    pub vars: &'hir [TypeVar],
    pub kind: TypeDeclKind<'hir>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub enum TypeDeclKind<'hir> {
    Alias(Ty<'hir>),
    Variant(&'hir Set<HirId>),
}

#[derive(Clone, Copy, Debug)]
pub struct Expr<'hir> {
    pub hir_id: HirId,
    pub kind: ExprKind<'hir>,
    pub span: Span,
    private: private::HirCtxtOnlyZst,
}

#[derive(Clone, Copy, Debug)]
pub enum ExprKind<'hir> {
    Path(Path<'hir>),
    Constructor(Path<'hir>),
    External(Sym, Ty<'hir>),
    Lit(Lit),
    Ann(&'hir Expr<'hir>, Ty<'hir>),
    Tuple(&'hir [Expr<'hir>]),
    Vector(&'hir [Expr<'hir>]),
    Lambda(&'hir Lambda<'hir>),
    Call(WebId, &'hir Expr<'hir>, &'hir [Expr<'hir>]),
    Let(&'hir [LetBind<'hir>], &'hir Expr<'hir>),
    If(&'hir Expr<'hir>, &'hir Expr<'hir>, &'hir Expr<'hir>),
    Case(&'hir Expr<'hir>, &'hir [CaseArm<'hir>]),
    Seq(&'hir Expr<'hir>, &'hir Expr<'hir>),
}

pub type LetBind<'hir> = (Pat<'hir>, Expr<'hir>);
pub type CaseArm<'hir> = (Pat<'hir>, Expr<'hir>);

#[derive(Clone, Copy, Debug)]
pub enum ExprArg<'hir> {
    Expr(Expr<'hir>),
    Type(Ty<'hir>),
}

#[derive(Clone, Copy, Debug)]
pub struct Lambda<'hir> {
    pub web_id: WebId,
    pub args: &'hir [Pat<'hir>],
    pub body: &'hir Expr<'hir>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Pat<'hir> {
    pub hir_id: HirId,
    pub kind: PatKind<'hir>,
    pub span: Span,
    private: private::HirCtxtOnlyZst,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PatKind<'hir> {
    Wild,
    Var(Path<'hir>),
    Lit(Lit),
    Ann(&'hir Pat<'hir>, Ty<'hir>),
    Tuple(&'hir [Pat<'hir>]),
    Constructor(Path<'hir>, &'hir [Pat<'hir>]),
    Or(&'hir [Pat<'hir>]),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lit {
    Unit,
    Bool(bool),
    Int32(i32),
    Str(Sym),
}

impl Lit {
    pub fn base_type(&self) -> BaseType {
        match self {
            Lit::Unit => BaseType::Unit,
            Lit::Bool(_) => BaseType::Bool,
            Lit::Str(_) => BaseType::Str,
            Lit::Int32(_) => BaseType::Int32,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct TypeDeclGroup<'hir> {
    pub decls: &'hir [TypeDecl<'hir>],
}

impl TypeDeclGroup<'_> {
    pub fn has_ident(&self, id: Ident) -> bool {
        self.decls.iter().any(|decl| decl.id == id)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ModExpr<'hir> {
    pub kind: ModExprKind<'hir>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub enum ModExprKind<'hir> {
    Path(Path<'hir>),
    Struct(&'hir Items<'hir>),
    Import(SourceId),
}

#[derive(Clone, Default, Debug)]
pub struct Items<'hir> {
    pub values: IndexMap<Ident, Value<'hir>>,
    pub types: HirSet,
    pub modules: IndexMap<Ident, &'hir ModExpr<'hir>>,

    pub type_groups: HirMap<HirSet>,
}

impl<'hir> Expr<'hir> {
    pub fn visit_with<V>(&'hir self, v: &mut V)
    where
        V: Visitor<&'hir Self>,
    {
        match self.kind {
            ExprKind::Path(_)
            | ExprKind::Constructor(_)
            | ExprKind::External(..)
            | ExprKind::Lit(_) => (),
            ExprKind::Ann(e, _) => v.visit(e),
            ExprKind::Tuple(es) | ExprKind::Vector(es) => es.iter().for_each(|e| v.visit(e)),
            ExprKind::Lambda(l) => v.visit(&l.body),
            ExprKind::Call(_, e, args) => {
                v.visit(e);
                args.iter().for_each(|e| v.visit(e));
            }
            ExprKind::If(c, e1, e2) => {
                v.visit(c);
                v.visit(e1);
                v.visit(e2);
            }
            ExprKind::Let(binds, e) => {
                binds.iter().for_each(|(_, e)| v.visit(e));
                v.visit(e);
            }
            ExprKind::Case(e, arms) => {
                v.visit(e);
                arms.iter().for_each(|(_, e)| v.visit(e));
            }
            ExprKind::Seq(e1, e2) => {
                v.visit(e1);
                v.visit(e2);
            }
        }
    }
}
