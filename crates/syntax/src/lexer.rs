use std::{iter::Peekable, str::Chars};

use span::{BytePos, Ident, SourceFile, Span, Sym};

use crate::token::{
    LitToken, Token,
    TokenKind::{self, *},
};

pub(crate) struct Lexer<'a> {
    source_file: &'a SourceFile,
    chars: Peekable<Chars<'a>>,
    pos: BytePos,
    consumed: bool,
    multiline_comment_depth: u32,
}

impl<'a> Lexer<'a> {
    pub fn new(source_file: &'a SourceFile) -> Self {
        Self {
            source_file,
            chars: source_file.src.chars().peekable(),
            pos: BytePos::from_u32(0),
            consumed: false,
            multiline_comment_depth: 0,
        }
    }

    fn span(&self, start: BytePos, end: BytePos) -> Span {
        Span::new(self.source_file.start + start, self.source_file.start + end)
    }

    fn slice(&self, start: BytePos) -> &'a str {
        self.slice_range(start, self.pos)
    }

    fn slice_range(&self, start: BytePos, end: BytePos) -> &'a str {
        &self.source_file.src[start.to_usize()..end.to_usize()]
    }

    pub fn advance(&mut self) -> Option<Token> {
        let start = self.pos;

        let Some(next) = self.bump() else {
            if !self.consumed {
                self.consumed = true;
                return Some(Token {
                    kind: EOF,
                    span: self.span(start, start),
                });
            } else {
                return None;
            }
        };

        if self.multiline_comment_depth > 0 {
            if next == '-'
                && let Some('}') = self.bump()
            {
                self.multiline_comment_depth -= 1;
            }

            return self.advance();
        }

        let kind = match next {
            c if c.is_whitespace() => {
                self.take_while(|c| c.is_whitespace());
                if self.slice(start).contains(['\n', '\r']) {
                    NEWLINE
                } else {
                    return self.advance();
                }
            }
            '(' => match self.peek() {
                Some(')') => {
                    self.bump();
                    UNIT
                }
                _ => L_PAREN,
            },
            ')' => R_PAREN,
            '{' => match self.peek() {
                Some('-') => {
                    self.bump();
                    self.multiline_comment_depth += 1;
                    return self.advance();
                }
                _ => L_BRACE,
            },
            '}' => R_BRACE,
            '[' => L_BRAC,
            ']' => R_BRAC,
            ',' => COMMA,
            '.' => DOT,
            ':' => match self.peek() {
                Some(&c) if is_infix(c) => {
                    self.take_while(is_infix);
                    INFIX(self.intern(start), ':')
                }
                _ => COLON,
            },
            ';' => SEMICOLON,
            '!' => EXCLAM,
            '\\' => BACKSLASH,
            '-' => match self.peek() {
                Some('>') => {
                    self.bump();
                    ARROW
                }
                Some('-') => {
                    self.bump();
                    self.take_while(|c| c != '\n');
                    return self.advance();
                }
                Some(c) if c.is_ascii_digit() => {
                    self.take_while(|c| c.is_ascii_digit() || c == '_');
                    LIT(LitToken::Int32(self.intern(start).sym))
                }
                _ => INFIX(self.intern(start), '-'),
            },
            '=' => match self.peek() {
                Some('>') => {
                    self.bump();
                    EQUAL_ARROW
                }
                Some(&c) if is_infix(c) => {
                    self.take_while(is_infix);
                    INFIX(self.intern(start), '=')
                }
                _ => EQUAL,
            },
            '@' => AT,
            '|' => match self.peek() {
                Some(&c) if is_infix(c) => {
                    self.take_while(is_infix);
                    INFIX(self.intern(start), '|')
                }
                _ => PIPE,
            },
            '_' => match self.peek() {
                Some(&c) if is_ident(c) => {
                    self.take_while(is_ident);
                    self.ident_or_keyword(start)
                }
                _ => UNDERSCORE,
            },
            '"' => self.lit_str(start),
            c if c.is_ascii_digit() => {
                self.take_while(|c| c.is_ascii_digit() || c == '_');
                LIT(LitToken::Int32(self.intern(start).sym))
            }
            '\'' => {
                self.bump();
                self.take_while(is_ident);
                VAR(self.intern(start))
            }
            c if is_ident(c) => {
                self.take_while(is_ident);
                self.ident_or_keyword(start)
            }
            c if is_infix(c) => {
                self.take_while(is_infix);
                INFIX(self.intern(start), c)
            }
            _ => UNKNOWN,
        };

        Some(Token {
            kind,
            span: self.span(start, self.pos),
        })
    }

    #[inline]
    fn bump(&mut self) -> Option<char> {
        self.chars
            .next()
            .inspect(|_| self.pos = self.pos + BytePos::from_u32(1))
    }

    #[inline]
    fn peek(&mut self) -> Option<&char> {
        self.chars.peek()
    }

    fn take_while(&mut self, pred: impl Fn(char) -> bool) {
        while let Some(&c) = self.peek()
            && pred(c)
        {
            self.bump();
        }
    }

    fn intern(&mut self, start: BytePos) -> Ident {
        self.intern_range(start, self.pos)
    }

    fn intern_range(&mut self, start: BytePos, end: BytePos) -> Ident {
        Ident::new(
            Sym::intern(self.slice_range(start, end)),
            self.span(start, end),
        )
    }

    fn keyword(&self, raw: &str) -> Option<TokenKind> {
        Some(match raw {
            "and" => KW_AND,
            "as" => KW_AS,
            "case" => KW_CASE,
            "else" => KW_ELSE,
            "end" => KW_END,
            "external" => KW_EXTERNAL,
            "forall" => KW_FORALL,
            "if" => KW_IF,
            "import" => KW_IMPORT,
            "include" => KW_INCLUDE,
            "in" => KW_IN,
            "is" => KW_IS,
            "let" => KW_LET,
            "main" => KW_MAIN,
            "mod" => KW_MOD,
            "open" => KW_OPEN,
            "of" => KW_OF,
            "then" => KW_THEN,
            "type" => KW_TYPE,
            "sig" => KW_SIG,
            "struct" => KW_STRUCT,
            "use" => KW_USE,
            "val" => KW_VAL,
            "with" => KW_WITH,
            "true" => LIT(LitToken::Bool(true)),
            "false" => LIT(LitToken::Bool(false)),
            _ => return None,
        })
    }

    fn ident_or_keyword(&mut self, start: BytePos) -> TokenKind {
        let raw = self.slice(start);
        match self.keyword(raw) {
            Some(t) => t,
            None => IDENT(
                self.intern(start),
                raw.starts_with(|c: char| c.is_uppercase()),
            ),
        }
    }

    fn lit_str(&mut self, start: BytePos) -> TokenKind {
        let terminated = (|| {
            while let Some(c) = self.bump() {
                match c {
                    '"' => return true,
                    '\\' => {
                        if let Some(&c) = self.peek()
                            && (c == '"' || c == '\\')
                        {
                            self.bump();
                        }
                    }
                    _ => (),
                }
            }
            false
        })();
        LIT(LitToken::Str(
            self.intern_range(
                start + BytePos::from_usize(1),
                self.pos - BytePos::from_usize(1),
            )
            .sym,
            terminated,
        ))
    }
}

#[inline]
fn is_ident(c: char) -> bool {
    matches!(c, '_' | '\'' | 'a'..='z' | 'A'..='Z' | '0'..='9')
}

#[inline]
fn is_infix(c: char) -> bool {
    matches!(
        c,
        '+' | '-' | '*' | '/' | '=' | '<' | '>' | '&' | '|' | '@' | '^' | ':'
    )
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.advance()
    }
}
