use std::fmt;

use span::{Ident, Span, Sym};

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn dummy() -> Self {
        Self {
            kind: TokenKind::EOF,
            span: Span::dummy(),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[allow(non_camel_case_types)]
#[allow(clippy::upper_case_acronyms)]
pub enum TokenKind {
    L_PAREN,
    R_PAREN,
    L_BRACE,
    R_BRACE,
    L_BRAC,
    R_BRAC,

    AT,
    BACKSLASH,
    COLON,
    COMMA,
    DOT,
    EQUAL,
    EXCLAM,
    PIPE,
    SEMICOLON,
    UNDERSCORE,

    // ->
    ARROW,
    // =>
    EQUAL_ARROW,
    // ()
    UNIT,

    // FIXME. clean up unused keywords.
    KW_AND,
    KW_AS,
    KW_CASE,
    KW_ELSE,
    KW_END,
    KW_EXTERNAL,
    KW_FORALL,
    KW_IF,
    KW_IMPORT,
    KW_INCLUDE,
    KW_IN,
    KW_IS,
    KW_LET,
    KW_MAIN,
    KW_MOD,
    KW_OF,
    KW_OPEN,
    KW_SIG,
    KW_STRUCT,
    KW_THEN,
    KW_TYPE,
    KW_USE,
    KW_VAL,
    KW_WITH,

    VAR(Ident),
    INFIX(Ident, char),
    IDENT(Ident, bool /* is_upper */),
    LIT(LitToken),
    //PREFIX(Sym),
    NEWLINE,
    EOF,
    UNKNOWN,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LitToken {
    Bool(bool),
    Int32(Sym),
    Str(Sym, bool /* terminated */),
}

impl TokenKind {
    pub fn is_keyword(&self) -> bool {
        use TokenKind::*;
        matches!(
            self,
            KW_AND
                | KW_AS
                | KW_CASE
                | KW_ELSE
                | KW_END
                | KW_EXTERNAL
                | KW_FORALL
                | KW_IF
                | KW_IMPORT
                | KW_INCLUDE
                | KW_IN
                | KW_IS
                | KW_LET
                | KW_MAIN
                | KW_MOD
                | KW_OF
                | KW_OPEN
                | KW_THEN
                | KW_TYPE
                | KW_SIG
                | KW_STRUCT
                | KW_USE
                | KW_VAL
                | KW_WITH
        )
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TokenKind::*;
        match self {
            L_PAREN => "(".fmt(f),
            R_PAREN => ")".fmt(f),
            L_BRACE => "{{".fmt(f),
            R_BRACE => "}}".fmt(f),
            L_BRAC => "[".fmt(f),
            R_BRAC => "]".fmt(f),
            AT => "@".fmt(f),
            BACKSLASH => "\\".fmt(f),
            COLON => ":".fmt(f),
            COMMA => ",".fmt(f),
            DOT => ".".fmt(f),
            EQUAL => "=".fmt(f),
            EXCLAM => "!".fmt(f),
            PIPE => "|".fmt(f),
            SEMICOLON => ";".fmt(f),
            UNDERSCORE => "_".fmt(f),
            ARROW => "->".fmt(f),
            EQUAL_ARROW => "=>".fmt(f),
            UNIT => "()".fmt(f),
            KW_AND => "and".fmt(f),
            KW_AS => "as".fmt(f),
            KW_CASE => "case".fmt(f),
            KW_ELSE => "else".fmt(f),
            KW_END => "end".fmt(f),
            KW_EXTERNAL => "external".fmt(f),
            KW_FORALL => "forall".fmt(f),
            KW_IF => "if".fmt(f),
            KW_IMPORT => "import".fmt(f),
            KW_INCLUDE => "include".fmt(f),
            KW_IN => "in".fmt(f),
            KW_IS => "is".fmt(f),
            KW_LET => "let".fmt(f),
            KW_MAIN => "main".fmt(f),
            KW_MOD => "mod".fmt(f),
            KW_OF => "of".fmt(f),
            KW_OPEN => "open".fmt(f),
            KW_THEN => "then".fmt(f),
            KW_TYPE => "type".fmt(f),
            KW_SIG => "sig".fmt(f),
            KW_STRUCT => "struct".fmt(f),
            KW_USE => "use".fmt(f),
            KW_VAL => "val".fmt(f),
            KW_WITH => "with".fmt(f),
            VAR(id) => write!(f, "'{}", id.sym.as_str()),
            INFIX(id, _) | IDENT(id, _) => id.sym.as_str().fmt(f),
            LIT(lit) => write!(f, "{lit:?}"),
            NEWLINE => "newline".fmt(f),
            EOF => "EOF".fmt(f),
            UNKNOWN => "UNKNOWN".fmt(f),
        }
    }
}
