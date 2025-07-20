//! Pretty printing utilities.
use std::{
    borrow::Cow,
    cell::Cell,
    fmt::{self, Write},
    io,
};

use crate::arena::TypedArena;

pub const INDENT: u32 = 3;
pub const PRETTY_WIDTH: u32 = 80;

pub trait WritePretty {
    fn pretty_print<W: io::Write>(&self, width: u32, w: &mut W) -> io::Result<()>;

    fn pretty_string(&self, width: u32) -> String {
        let mut v = Vec::new();
        self.pretty_print(width, &mut v).unwrap();
        String::from_utf8(v).unwrap()
    }
}

pub struct Pretty<T>(pub T);

impl<T> fmt::Display for Pretty<T>
where
    T: WritePretty,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.pretty_string(PRETTY_WIDTH).fmt(f)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Subscript(pub u32);

const SUBSCRIPTS: &[char] = &['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'];

impl fmt::Display for Subscript {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for digit in self.0.to_string().chars().map(|d| d.to_digit(10).unwrap()) {
            f.write_char(SUBSCRIPTS[digit as usize])?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Superscript(pub u32);

const SUPERSCRIPTS: &[char] = &['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];

impl fmt::Display for Superscript {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for digit in self.0.to_string().chars().map(|d| d.to_digit(10).unwrap()) {
            f.write_char(SUPERSCRIPTS[digit as usize])?;
        }
        Ok(())
    }
}

pub fn desubscriptify(mut s: String) -> String {
    for &sub in SUBSCRIPTS {
        s = s.replace(sub, "");
    }
    s
}

// Format from itertools.
pub trait FormatIterator: Sized + Iterator {
    fn format(self, sep: &str) -> Format<'_, Self> {
        Format {
            sep,
            inner: Cell::new(Some(self)),
        }
    }
}

impl<T: Iterator> FormatIterator for T {}

pub struct Format<'a, I> {
    sep: &'a str,
    inner: Cell<Option<I>>,
}

impl<I: Iterator> Format<'_, I> {
    fn format(
        &self,
        f: &mut fmt::Formatter<'_>,
        cb: fn(&I::Item, &mut fmt::Formatter<'_>) -> fmt::Result,
    ) -> fmt::Result {
        let mut iter = self.inner.take().expect("already formatted");
        if let Some(first) = iter.next() {
            cb(&first, f)?;
            iter.try_for_each(|e| {
                if !self.sep.is_empty() {
                    f.write_str(self.sep)?;
                }
                cb(&e, f)
            })?;
        }
        Ok(())
    }
}

impl<I> fmt::Display for Format<'_, I>
where
    I: Iterator,
    I::Item: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(f, fmt::Display::fmt)
    }
}

impl<I> fmt::Debug for Format<'_, I>
where
    I: Iterator,
    I::Item: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(f, fmt::Debug::fmt)
    }
}

/// Impl from <https://justinpombrio.net/2024/02/23/a-twist-on-Wadlers-printer.html>.
/// See also Strictly Pretty <https://lindig.github.io/papers/strictly-pretty-2000.pdf>.
/// API design from <https://github.com/Marwes/pretty.rs>.
#[derive(Clone, Debug)]
pub enum Doc<'a> {
    Empty,
    Line,
    Text(Cow<'a, str>),
    Nest(u32, &'a Doc<'a>),
    Group(&'a Doc<'a>),
    Append(&'a Doc<'a>, &'a Doc<'a>),
    Choice(&'a Doc<'a>, &'a Doc<'a>),
}

pub trait IntoDoc<'a> {
    fn into_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a>;
}

#[derive(Default)]
pub struct DocArena<'a> {
    arena: TypedArena<Doc<'a>>,
}

impl<'a> DocArena<'a> {
    pub fn alloc(&'a self, doc: Doc<'a>) -> &'a Doc<'a> {
        self.arena.alloc(doc)
    }

    pub fn text<S: Into<Cow<'a, str>>>(&'a self, s: S) -> DocBuilder<'a> {
        DocBuilder(self, Doc::Text(s.into()))
    }

    pub fn space(&'a self) -> DocBuilder<'a> {
        self.text(" ")
    }

    pub fn empty(&'a self) -> DocBuilder<'a> {
        DocBuilder(self, Doc::Empty)
    }

    pub fn line(&'a self) -> DocBuilder<'a> {
        DocBuilder(self, Doc::Line)
    }

    pub fn intersperse<I, S>(&'a self, docs: I, sep: S) -> DocBuilder<'a>
    where
        I: IntoIterator,
        I::Item: IntoDoc<'a>,
        S: IntoDoc<'a> + Clone,
    {
        let mut docs = docs.into_iter();
        if let Some(first) = docs.next() {
            let mut result = first.into_doc(self);
            for doc in docs {
                result = result.append(sep.clone()).append(doc);
            }
            result
        } else {
            self.empty()
        }
    }
}

#[derive(Clone)]
pub struct DocBuilder<'a>(pub &'a DocArena<'a>, pub Doc<'a>);

impl<'a> std::ops::Deref for DocBuilder<'a> {
    type Target = Doc<'a>;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

impl<'a> IntoDoc<'a> for DocBuilder<'a> {
    fn into_doc(self, _: &'a DocArena<'a>) -> DocBuilder<'a> {
        self
    }
}

impl<'a> IntoDoc<'a> for &'a str {
    fn into_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        arena.text(self)
    }
}

impl<'a> IntoDoc<'a> for String {
    fn into_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        arena.text(self)
    }
}

impl<'a> DocBuilder<'a> {
    pub fn doc(self) -> &'a Doc<'a> {
        self.0.alloc(self.1)
    }

    pub fn append<D: IntoDoc<'a>>(self, other: D) -> DocBuilder<'a> {
        let alloc = self.0;
        DocBuilder(alloc, Doc::Append(self.doc(), other.into_doc(alloc).doc()))
    }

    pub fn choice<D: IntoDoc<'a>>(self, other: D) -> DocBuilder<'a> {
        let alloc = self.0;
        DocBuilder(alloc, Doc::Choice(self.doc(), other.into_doc(alloc).doc()))
    }

    pub fn nest(self, indent: u32) -> DocBuilder<'a> {
        DocBuilder(self.0, Doc::Nest(indent, self.doc()))
    }

    pub fn group(self) -> Self {
        DocBuilder(self.0, Doc::Group(self.doc()))
    }

    pub fn enclose<L: IntoDoc<'a>, R: IntoDoc<'a>>(self, left: L, right: R) -> DocBuilder<'a> {
        left.into_doc(self.0).append(self).append(right)
    }

    pub fn space<D: IntoDoc<'a>>(self, other: D) -> DocBuilder<'a> {
        let space = self.0.space();
        self.append(space).append(other)
    }

    pub fn pretty<W: io::Write>(self, writer: &mut W, width: u32) -> io::Result<()> {
        let mut printer = Printer::new(self.doc(), width);
        printer.format(writer)
    }

    pub fn pretty_string(self, width: u32) -> String {
        let mut buffer = Vec::new();
        self.pretty(&mut buffer, width).unwrap();
        String::from_utf8(buffer).unwrap()
    }
}

struct Printer<'a> {
    width: u32,
    col: u32,
    chunks: Vec<Chunk<'a>>,
}

#[derive(Clone, Copy)]
struct Chunk<'a> {
    doc: &'a Doc<'a>,
    indent: u32,
    flat: bool,
}

impl<'a> Chunk<'a> {
    fn with_doc(self, doc: &'a Doc<'a>) -> Self {
        Self {
            doc,
            indent: self.indent,
            flat: self.flat,
        }
    }

    fn indent(self, indent: u32) -> Self {
        Self {
            doc: self.doc,
            indent: self.indent + indent,
            flat: self.flat,
        }
    }

    fn flat(self) -> Self {
        Self {
            doc: self.doc,
            indent: self.indent,
            flat: true,
        }
    }
}

impl<'a> Printer<'a> {
    fn new(doc: &'a Doc<'a>, width: u32) -> Self {
        Self {
            width,
            col: 0,
            chunks: vec![Chunk {
                doc,
                indent: 0,
                flat: false,
            }],
        }
    }

    fn fits(&self, chunk: Chunk<'a>) -> bool {
        let mut remaining = if self.col <= self.width {
            self.width - self.col
        } else {
            return false;
        };
        let mut stack = vec![chunk];
        let mut chunks = &self.chunks as &[Chunk];
        loop {
            let chunk = match stack.pop() {
                Some(chunk) => chunk,
                None => match chunks.split_last() {
                    None => return true,
                    Some((chunk, more_chunks)) => {
                        chunks = more_chunks;
                        *chunk
                    }
                },
            };

            match chunk.doc {
                Doc::Empty => continue,
                Doc::Line => return true,
                Doc::Text(s) => {
                    let width = s.len() as u32;
                    if width <= remaining {
                        remaining -= width;
                    } else {
                        return false;
                    }
                }
                Doc::Nest(i, d) => stack.push(chunk.with_doc(d).indent(*i)),
                Doc::Group(d) => stack.push(chunk.with_doc(d).flat()),
                Doc::Append(l, r) => {
                    stack.push(chunk.with_doc(r));
                    stack.push(chunk.with_doc(l));
                }
                Doc::Choice(l, r) => {
                    if chunk.flat {
                        stack.push(chunk.with_doc(l));
                    } else {
                        // Relies on the rule that for every choice `x | y`,
                        // the first line of `y` is no longer than the first
                        // line of `x`.
                        stack.push(chunk.with_doc(r));
                    }
                }
            }
        }
    }

    fn format<W: io::Write>(&mut self, writer: &mut W) -> io::Result<()> {
        while let Some(chunk) = self.chunks.pop() {
            match chunk.doc {
                Doc::Empty => (),
                Doc::Text(s) => {
                    writer.write_all(s.as_bytes())?;
                    self.col += s.len() as u32;
                }
                Doc::Line => {
                    writer.write_all(b"\n")?;
                    for _ in 0..chunk.indent {
                        writer.write_all(b" ")?;
                    }
                    self.col = chunk.indent;
                }
                Doc::Nest(i, d) => self.chunks.push(chunk.with_doc(d).indent(*i)),
                Doc::Group(d) => self.chunks.push(chunk.with_doc(d).flat()),
                Doc::Append(l, r) => {
                    self.chunks.push(chunk.with_doc(r));
                    self.chunks.push(chunk.with_doc(l));
                }
                Doc::Choice(l, r) => {
                    if chunk.flat || self.fits(chunk.with_doc(l)) {
                        self.chunks.push(chunk.with_doc(l))
                    } else {
                        self.chunks.push(chunk.with_doc(r))
                    }
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn indent() {
        let arena = DocArena::default();
        let singleline = arena
            .text("hello")
            .append(",")
            .space("world")
            .enclose("(", ")")
            .group();
        let multiline = arena
            .line()
            .append("hello")
            .append(",")
            .append(arena.line())
            .append("world")
            .append(",")
            .nest(4)
            .append(arena.line())
            .enclose("(", ")")
            .group();
        let doc = singleline.choice(multiline);

        assert_eq!("(hello, world)", doc.clone().pretty_string(100));
        assert_eq!(
            r#"(
    hello,
    world,
)"#,
            doc.pretty_string(10)
        );
    }
}
