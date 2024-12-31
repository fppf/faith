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

macro_rules! cache {
    ($name:ident { $typ:ident, $new:ident }, $($id:ident = $e:expr,)+) => {
        pub struct $name<'hir> {
            $(pub $id: $typ<'hir>,)+
        }

        impl<'hir> $name<'hir> {
            pub fn new(arena: &'hir Arena<'hir>) -> Self {
                Self {
                    $($id: $typ::$new(arena, $e, Span::dummy()),)+
                }
            }
        }
    }
}

cache! {
    TypeCache { Ty, new },

    abs = TyKind::Abstract,
    unit = TyKind::Base(BaseType::Unit),
    bool = TyKind::Base(BaseType::Bool),
    str = TyKind::Base(BaseType::Str),
    i32 = TyKind::Base(BaseType::Int32),
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
