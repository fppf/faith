use std::fmt;

use crate::ast::*;

impl fmt::Display for Path<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.root.fmt(f)?;
        for id in self.access {
            write!(f, ".{id}")?;
        }
        Ok(())
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => "()".fmt(f),
            Self::Bool(b) => b.fmt(f),
            Self::Int32(n) => write!(f, "{n}i32"),
            Self::Str(s) => write!(f, "\"{}\"", s.as_str()),
        }
    }
}

impl fmt::Display for BaseType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseType::Unit => "()",
            BaseType::Bool => "bool",
            BaseType::Str => "str",
            BaseType::Int32 => "i32",
        }
        .fmt(f)
    }
}
