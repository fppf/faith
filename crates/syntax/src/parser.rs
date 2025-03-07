use std::cell::Cell;

use base::hash::Map;
use span::{
    BytePos, SourceId, Span,
    diag::{Diagnostic, Label, Level},
};

use crate::{
    Arena,
    ast::{AstId, CompUnit},
};

use super::token::{Token, TokenKind};

pub type ParseResult<T> = Result<T, ParseError>;

pub(crate) struct Parser<'ast> {
    tokens: Vec<Token>,
    pos: usize,
    steps: Cell<u32>,
    pub ast_id: AstId,
    pub arena: &'ast Arena<'ast>,
    pub current_comp_unit: SourceId,
    pub inside_std: bool,
    pub imports: Map<SourceId, &'ast CompUnit<'ast>>,
}

#[derive(Clone, Copy)]
pub struct Marker {
    start: Span,
}

impl Marker {
    fn new(start: Span) -> Self {
        Self { start }
    }

    fn complete(&self, end: Span) -> Span {
        self.start.merge(end)
    }
}

impl<'ast> Parser<'ast> {
    pub fn new(
        arena: &'ast Arena<'ast>,
        current_comp_unit: SourceId,
        tokens: impl IntoIterator<Item = Token>,
    ) -> Self {
        Self {
            tokens: tokens.into_iter().collect(),
            pos: 0,
            steps: Cell::default(),
            ast_id: AstId::ZERO,
            arena,
            current_comp_unit,
            inside_std: false,
            imports: Map::default(),
        }
    }

    pub fn next_ast_id(&mut self) -> AstId {
        self.ast_id = self.ast_id + 1;
        self.ast_id
    }

    pub fn nth(&self, n: usize) -> Token {
        let steps = self.steps.get();
        assert!(steps < 10_000_000, "Parser step limit reached");
        self.steps.set(steps + 1);
        self.tokens
            .get(self.pos + n)
            .copied()
            .unwrap_or(Token::dummy())
    }

    pub fn current(&self) -> Token {
        self.nth(0)
    }

    pub fn at(&self, kind: TokenKind) -> bool {
        kind == self.current().kind
    }

    pub fn eat(&mut self, kind: TokenKind) -> bool {
        if self.at(kind) {
            self.bump_pos();
            true
        } else {
            false
        }
    }

    pub fn bump(&mut self, kind: TokenKind) {
        assert!(self.eat(kind));
    }

    pub fn bump_any(&mut self) {
        if self.current().kind != TokenKind::EOF {
            self.bump_pos();
        }
    }

    pub fn expect(&mut self, kind: TokenKind) -> ParseResult<()> {
        if self.eat(kind) {
            Ok(())
        } else {
            let other_kind = self.current().kind;
            Err(ParseError::new(
                format!(
                    "expected {} '{kind}', got {}'{other_kind}'",
                    if kind.is_keyword() {
                        "keyword"
                    } else {
                        "token"
                    },
                    if other_kind.is_keyword() {
                        "keyword "
                    } else {
                        ""
                    },
                ),
                self.current().span,
            ))
        }
    }

    pub fn start(&self) -> Marker {
        Marker::new(self.current().span)
    }

    pub fn end(&self, marker: Marker) -> Span {
        marker.complete(if self.at(TokenKind::EOF) {
            let mut span = self.current().span;
            span.end = span.end - BytePos::from_u32(1);
            span
        } else {
            self.current().span
        })
    }

    fn bump_pos(&mut self) {
        self.pos += 1;
        while self.current().kind == TokenKind::NEWLINE {
            self.bump_pos();
        }
    }
}

pub struct ParseError {
    text: String,
    span: Span,
}

impl ParseError {
    pub fn new(text: impl Into<String>, span: Span) -> Self {
        Self {
            text: text.into(),
            span,
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn span(&self) -> Span {
        self.span
    }
}

impl From<ParseError> for Diagnostic {
    fn from(e: ParseError) -> Self {
        Self::new(Level::Error)
            .with_message(e.text())
            .with_labels(vec![Label::new(e.span(), "").primary()])
    }
}
