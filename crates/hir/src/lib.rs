#![feature(let_chains)]
#![allow(unused)]

mod hir;
mod lower;
mod path;
mod pretty;
mod typ;

pub use hir::*;
pub use lower::lower_program_in;

use span::diag::Diagnostic;

pub fn parse_and_lower_program_in<'hir>(
    hir_arena: &'hir Arena<'hir>,
    path: &std::path::Path,
) -> Result<&'hir Program<'hir>, Diagnostic> {
    let ast_arena = syntax::Arena::default();
    let ast = syntax::parse_program_in(&ast_arena, path)?;
    lower::lower_program_in(hir_arena, ast)
}

pub fn parse_and_lower_str_program_in<'hir>(
    hir_arena: &'hir Arena<'hir>,
    src: &str,
) -> Result<&'hir Program<'hir>, Diagnostic> {
    let ast_arena = syntax::Arena::default();
    let ast = syntax::parse_str_program_in(&ast_arena, src)?;
    lower::lower_program_in(hir_arena, ast)
}

base::declare_arena!('hir, [
    set: HirSet,
    items: Items<'hir>,
    specs: Specs<'hir>,
    program: Program<'hir>,
]);

use span::{Ident, Span};

impl<'hir> Arena<'hir> {
    #[inline]
    pub fn path<I>(&'hir self, id: Ident, access: I, span: Span, res: Res) -> Path<'hir>
    where
        I: IntoIterator<Item = Ident>,
    {
        Path::new(self, id, self.alloc_from_iter(access), span, res)
    }

    #[inline]
    pub fn typ(&'hir self, kind: TyKind<'hir>, span: Span) -> Ty<'hir> {
        Ty::new(self, kind, span)
    }

    #[inline]
    pub fn expr(&'hir self, kind: ExprKind<'hir>, span: Span) -> Expr<'hir> {
        Expr::new(self, kind, span)
    }
}
