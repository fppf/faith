use std::{fmt, hash::Hash};

use base::arena::Interned;
use span::{Ident, Span};

use crate::{Arena, HirId};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Res {
    Def(DefKind, HirId),
    Local(HirId),
}

impl Res {
    pub fn hir_id(&self) -> HirId {
        match *self {
            Res::Def(_, hir_id) | Res::Local(hir_id) => hir_id,
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
            Res::Def(kind, hir_id) => {
                write!(f, "{kind:?}:{hir_id}")
            }
            Res::Local(hir_id) => hir_id.fmt(f),
        }
    }
}

/// A qualified, resolved path.
#[derive(Clone, Copy, Hash)]
pub struct Path<'hir>(Interned<'hir, PathInner<'hir>>);

#[cfg(test)]
mod test {
    use crate::{DefKind, HirCtxt, HirId, Res};
    use span::{Ident, Span, Sym};

    #[test]
    fn equality() {
        let ctxt = HirCtxt::default();
        let id = Ident::new(Sym::intern("x"), Span::from(1..2));
        let res = Res::Def(DefKind::Value, HirId::from_u32(1));
        let p1 = ctxt.path(id, [id, id], Span::from(1..4), res);
        let p2 = ctxt.path(id, [id, id], Span::from(2..4), res);
        assert_eq!(p1, p2);
    }
}

#[derive(Clone, Copy)]
struct PathInner<'hir> {
    root: Ident,
    access: &'hir [Ident],
    span: Span,
    res: Res,
}

impl PartialEq for Path<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
            && self.access_slice() == other.access_slice()
            && self.res() == other.res()
    }
}

impl Eq for Path<'_> {}

impl<'hir> Path<'hir> {
    #[inline]
    pub(crate) fn new(
        arena: &'hir Arena<'hir>,
        id: Ident,
        access: &'hir [Ident],
        span: Span,
        res: Res,
    ) -> Self {
        Path(Interned::new_unchecked(arena.alloc(PathInner {
            root: id,
            access,
            span,
            res,
        })))
    }

    #[inline]
    pub fn span(&self) -> Span {
        self.0.span
    }

    #[inline]
    pub fn res(&self) -> Res {
        self.0.res
    }

    #[inline]
    pub fn leaf(&self) -> Ident {
        if self.is_ident() {
            self.0.root
        } else {
            *self.0.access.last().unwrap()
        }
    }

    #[inline]
    pub fn is_ident(&self) -> bool {
        self.0.access.is_empty()
    }

    #[inline]
    pub fn as_ident(&self) -> Option<Ident> {
        if self.is_ident() {
            Some(self.0.root)
        } else {
            None
        }
    }

    #[inline]
    pub fn id(&self) -> Ident {
        self.0.root
    }

    #[inline]
    pub fn access(&self) -> impl Iterator<Item = Ident> + '_ {
        self.0.access.iter().copied()
    }

    #[inline]
    pub fn access_slice(&self) -> &[Ident] {
        self.0.access
    }
}

impl fmt::Debug for Path<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id().fmt(f)?;
        for s in self.access() {
            write!(f, ".{}", s.as_str())?;
        }
        write!(f, "<{}>", self.res())
    }
}

impl fmt::Display for Path<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id().fmt(f)?;
        for s in self.access() {
            write!(f, ".{}", s.as_str())?;
        }
        Ok(())
    }
}
