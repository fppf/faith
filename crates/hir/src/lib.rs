#![feature(let_chains)]
#![allow(unused)]

mod hir;
mod lower;
mod path;
mod pretty;
mod typ;

use std::cell::{Cell, OnceCell, RefCell};

use base::index::{Idx, IndexVec};
pub use hir::*;

use span::diag::Diagnostic;

pub struct HirCtxt<'hir> {
    pub arena: Arena<'hir>,
    hir_nodes: RefCell<IndexVec<HirId, HirNode<'hir>>>,
}

#[derive(Default)]
struct HirNode<'hir> {
    typ: OnceCell<Ty<'hir>>,
}

impl<'hir> Default for HirCtxt<'hir> {
    fn default() -> Self {
        Self {
            arena: Arena::default(),
            hir_nodes: RefCell::default(),
        }
    }
}

impl<'hir> HirCtxt<'hir> {
    fn new_hir_node(&self) -> HirId {
        let mut nodes = self.hir_nodes.borrow_mut();
        nodes.push(HirNode::default())
    }

    pub fn is_ctxt_typed(&self) -> bool {
        self.hir_nodes.borrow().iter_enumerated().all(|(id, node)| {
            if !node.typ.get().is_some() {
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

use span::{Ident, Span};

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
        Expr::new(&self.arena, kind, span)
    }
}
