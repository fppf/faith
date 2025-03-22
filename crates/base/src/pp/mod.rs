//! Pretty printing utilities.
use std::{
    borrow::Cow,
    cell::Cell,
    collections::VecDeque,
    fmt::{self, Write},
    io,
};

use crate::arena::TypedArena;

pub const INDENT: isize = 3;
pub const PRETTY_WIDTH: usize = 80;

pub trait WritePretty {
    fn pretty_print<W: io::Write>(&self, width: usize, w: &mut W) -> io::Result<()>;
}

pub struct Pretty<T>(pub T);

impl<T> fmt::Display for Pretty<T>
where
    T: WritePretty,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut v = Vec::new();
        self.0.pretty_print(PRETTY_WIDTH, &mut v).unwrap();
        String::from_utf8(v).unwrap().fmt(f)
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

/// Strictly Pretty <https://lindig.github.io/papers/strictly-pretty-2000.pdf>.
/// API design from <https://github.com/Marwes/pretty.rs>
#[derive(Clone, Debug)]
pub enum Doc<'a> {
    Empty,
    Line,
    Text(Cow<'a, str>),
    Break(&'a str),
    Nest(isize, &'a Doc<'a>),
    Append(&'a Doc<'a>, &'a Doc<'a>),
    Group(&'a Doc<'a>),
}

pub trait ToDoc<'a> {
    fn to_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a>;
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

    pub fn brk(&'a self, s: &'a str) -> DocBuilder<'a> {
        DocBuilder(self, Doc::Break(s))
    }

    pub fn space(&'a self) -> DocBuilder<'a> {
        self.brk(" ")
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
        I::Item: ToDoc<'a>,
        S: ToDoc<'a> + Clone,
    {
        let mut docs = docs.into_iter();
        let mut result = self.empty();
        if let Some(first) = docs.next() {
            result = result.append(first);
            for doc in docs {
                result = result.append(sep.clone()).append(doc);
            }
        }
        result
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

impl<'a> ToDoc<'a> for DocBuilder<'a> {
    fn to_doc(self, _: &'a DocArena<'a>) -> DocBuilder<'a> {
        self
    }
}

impl<'a> ToDoc<'a> for &'a str {
    fn to_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        arena.text(self)
    }
}

impl<'a> ToDoc<'a> for String {
    fn to_doc(self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        arena.text(self)
    }
}

impl<'a> DocBuilder<'a> {
    pub fn doc(self) -> &'a Doc<'a> {
        self.0.alloc(self.1)
    }

    pub fn append<T: ToDoc<'a>>(self, other: T) -> DocBuilder<'a> {
        let alloc = self.0;
        DocBuilder(alloc, Doc::Append(self.doc(), other.to_doc(alloc).doc()))
    }

    pub fn nest(self, indent: isize) -> DocBuilder<'a> {
        DocBuilder(self.0, Doc::Nest(indent, self.doc()))
    }

    pub fn group(self) -> Self {
        DocBuilder(self.0, Doc::Group(self.doc()))
    }

    pub fn enclose<L: ToDoc<'a>, R: ToDoc<'a>>(self, left: L, right: R) -> DocBuilder<'a> {
        left.to_doc(self.0).append(self).append(right)
    }

    pub fn pretty<W: io::Write>(self, writer: &mut W, width: usize) -> io::Result<()> {
        let docs = VecDeque::from([(0, Mode::Flat, self.0.alloc(self.1))]);
        format(writer, width as isize, 0, docs)
    }

    pub fn pretty_string(self, width: usize) -> String {
        let mut buffer = Vec::new();
        self.pretty(&mut buffer, width).unwrap();
        String::from_utf8(buffer).unwrap()
    }
}

#[derive(Clone, Copy)]
pub enum Mode {
    Flat,
    Break,
}

fn fits(width: isize, mut docs: VecDeque<(isize, Mode, &Doc<'_>)>) -> bool {
    if width < 0 {
        return false;
    }
    let mut total = 0isize;
    while total <= width
        && let Some((indent, mode, doc)) = docs.pop_front()
    {
        match doc {
            Doc::Empty => continue,
            Doc::Line => return true,
            Doc::Text(s) => total += s.len() as isize,
            Doc::Break(s) => match mode {
                Mode::Flat => total += s.len() as isize,
                Mode::Break => return true,
            },
            Doc::Nest(inner_indent, doc) => docs.push_front((indent + inner_indent, mode, doc)),
            Doc::Append(l, r) => {
                docs.push_front((indent, mode, r));
                docs.push_front((indent, mode, l));
            }
            Doc::Group(doc) => {
                docs.push_front((indent, Mode::Flat, doc));
            }
        }
    }
    total <= width
}

fn format<W: io::Write>(
    writer: &mut W,
    width: isize,
    mut consumed: isize,
    mut docs: VecDeque<(isize, Mode, &Doc<'_>)>,
) -> io::Result<()> {
    while let Some((indent, mode, doc)) = docs.pop_front() {
        match doc {
            Doc::Empty => (),
            Doc::Text(s) => {
                writer.write_all(s.as_bytes())?;
                consumed += s.len() as isize;
            }
            Doc::Line => {
                write_indent(writer, indent)?;
                consumed = indent;
            }
            Doc::Break(s) => {
                writer.write_all(s.as_bytes())?;
                consumed = match mode {
                    Mode::Flat => consumed + s.len() as isize,
                    Mode::Break => {
                        write_indent(writer, indent)?;
                        indent
                    }
                };
            }
            Doc::Nest(inner_indent, doc) => {
                docs.push_front((indent + inner_indent, mode, doc));
            }
            Doc::Append(l, r) => {
                docs.push_front((indent, mode, r));
                docs.push_front((indent, mode, l));
            }
            Doc::Group(doc) => {
                let mode = if fits(
                    width - consumed,
                    VecDeque::from([(indent, Mode::Flat, *doc)]),
                ) {
                    Mode::Flat
                } else {
                    Mode::Break
                };
                docs.push_front((indent, mode, doc));
            }
        }
    }
    Ok(())
}

fn write_indent<W: io::Write>(writer: &mut W, indent: isize) -> Result<(), io::Error> {
    writer.write_all(b"\n")?;
    for _ in 0..indent {
        writer.write_all(b" ")?;
    }
    Ok(())
}
