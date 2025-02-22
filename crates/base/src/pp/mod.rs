//! Pretty printing utilities.
use std::{
    borrow::Cow,
    cell::Cell,
    collections::VecDeque,
    fmt::{self, Write},
    io,
    ops::{Deref, DerefMut, Index, IndexMut},
};

pub const INDENT: isize = 4;
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

#[derive(Clone, Copy, PartialEq)]
pub enum Breaks {
    Consistent,
    Inconsistent,
}

#[derive(Clone, Copy, PartialEq)]
enum IndentStyle {
    Visual,
    Block { offset: isize },
}

#[derive(Clone, Copy, Default, PartialEq)]
struct BreakToken {
    offset: isize,
    blank_space: isize,
    pre_break: Option<char>,
}

#[derive(Clone, Copy, PartialEq)]
struct BeginToken {
    indent: IndentStyle,
    breaks: Breaks,
}

#[derive(PartialEq)]
enum Token {
    String(Cow<'static, str>),
    Break(BreakToken),
    Begin(BeginToken),
    End,
}

impl Token {
    fn is_hardbreak_tok(&self) -> bool {
        *self == Printer::hardbreak_tok_offset(0)
    }
}

#[derive(Clone, Copy)]
enum PrintFrame {
    Fits,
    Broken { indent: usize, breaks: Breaks },
}

const SIZE_INFINITY: isize = 0xffff;
const MARGIN: isize = 78;
const MIN_SPACE: isize = 60;

struct RingBuffer<T> {
    data: VecDeque<T>,
    offset: usize,
}

impl<T> RingBuffer<T> {
    fn new() -> Self {
        RingBuffer {
            data: VecDeque::new(),
            offset: 0,
        }
    }

    fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    fn push(&mut self, value: T) -> usize {
        let index = self.offset + self.data.len();
        self.data.push_back(value);
        index
    }

    fn clear(&mut self) {
        self.data.clear();
    }

    fn index_of_first(&self) -> usize {
        self.offset
    }

    fn first(&self) -> Option<&T> {
        self.data.front()
    }

    fn first_mut(&mut self) -> Option<&mut T> {
        self.data.front_mut()
    }

    fn pop_first(&mut self) -> Option<T> {
        let first = self.data.pop_front()?;
        self.offset += 1;
        Some(first)
    }

    fn last(&self) -> Option<&T> {
        self.data.back()
    }

    fn last_mut(&mut self) -> Option<&mut T> {
        self.data.back_mut()
    }
}

impl<T> Index<usize> for RingBuffer<T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        &self.data[index.checked_sub(self.offset).unwrap()]
    }
}

impl<T> IndexMut<usize> for RingBuffer<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.data[index.checked_sub(self.offset).unwrap()]
    }
}

pub struct Printer {
    out: String,
    space: isize,
    buf: RingBuffer<BufEntry>,
    left_total: isize,
    right_total: isize,
    scan_stack: VecDeque<usize>,
    print_stack: Vec<PrintFrame>,
    indent: usize,
    pending_indentation: isize,
    last_printed: Option<Token>,
}

struct BufEntry {
    token: Token,
    size: isize,
}

impl Default for Printer {
    fn default() -> Self {
        Printer {
            out: String::new(),
            space: MARGIN,
            buf: RingBuffer::new(),
            left_total: 0,
            right_total: 0,
            scan_stack: VecDeque::new(),
            print_stack: Vec::new(),
            indent: 0,
            pending_indentation: 0,
            last_printed: None,
        }
    }
}

impl Printer {
    fn last_token(&self) -> Option<&Token> {
        self.last_token_still_buffered()
            .or(self.last_printed.as_ref())
    }

    fn last_token_still_buffered(&self) -> Option<&Token> {
        self.buf.last().map(|last| &last.token)
    }

    fn replace_last_token_still_buffered(&mut self, token: Token) {
        self.buf.last_mut().unwrap().token = token;
    }

    fn scan_eof(&mut self) {
        if !self.scan_stack.is_empty() {
            self.check_stack(0);
            self.advance_left();
        }
    }

    fn scan_begin(&mut self, token: BeginToken) {
        if self.scan_stack.is_empty() {
            self.left_total = 1;
            self.right_total = 1;
            self.buf.clear();
        }
        let right = self.buf.push(BufEntry {
            token: Token::Begin(token),
            size: -self.right_total,
        });
        self.scan_stack.push_back(right);
    }

    fn scan_end(&mut self) {
        if self.scan_stack.is_empty() {
            self.print_end();
        } else {
            let right = self.buf.push(BufEntry {
                token: Token::End,
                size: -1,
            });
            self.scan_stack.push_back(right);
        }
    }

    fn scan_break(&mut self, token: BreakToken) {
        if self.scan_stack.is_empty() {
            self.left_total = 1;
            self.right_total = 1;
            self.buf.clear();
        } else {
            self.check_stack(0);
        }
        let right = self.buf.push(BufEntry {
            token: Token::Break(token),
            size: -self.right_total,
        });
        self.scan_stack.push_back(right);
        self.right_total += token.blank_space;
    }

    fn scan_string(&mut self, string: Cow<'static, str>) {
        if self.scan_stack.is_empty() {
            self.print_string(&string);
        } else {
            let len = string.len() as isize;
            self.buf.push(BufEntry {
                token: Token::String(string),
                size: len,
            });
            self.right_total += len;
            self.check_stream();
        }
    }

    #[allow(unused)]
    fn offset(&mut self, offset: isize) {
        if let Some(BufEntry {
            token: Token::Break(token),
            ..
        }) = &mut self.buf.last_mut()
        {
            token.offset += offset;
        }
    }

    fn check_stream(&mut self) {
        while self.right_total - self.left_total > self.space {
            if *self.scan_stack.front().unwrap() == self.buf.index_of_first() {
                self.scan_stack.pop_front().unwrap();
                self.buf.first_mut().unwrap().size = SIZE_INFINITY;
            }
            self.advance_left();
            if self.buf.is_empty() {
                break;
            }
        }
    }

    fn advance_left(&mut self) {
        while self.buf.first().unwrap().size >= 0 {
            let left = self.buf.pop_first().unwrap();
            match &left.token {
                Token::String(string) => {
                    self.left_total += string.len() as isize;
                    self.print_string(string);
                }
                Token::Break(token) => {
                    self.left_total += token.blank_space;
                    self.print_break(*token, left.size);
                }
                Token::Begin(token) => self.print_begin(*token, left.size),
                Token::End => self.print_end(),
            }
            self.last_printed = Some(left.token);
            if self.buf.is_empty() {
                break;
            }
        }
    }

    fn check_stack(&mut self, mut depth: usize) {
        while let Some(&index) = self.scan_stack.back() {
            let entry = &mut self.buf[index];
            match entry.token {
                Token::Begin(_) => {
                    if depth == 0 {
                        break;
                    }
                    self.scan_stack.pop_back().unwrap();
                    entry.size += self.right_total;
                    depth -= 1;
                }
                Token::End => {
                    self.scan_stack.pop_back().unwrap();
                    entry.size = 1;
                    depth += 1;
                }
                _ => {
                    self.scan_stack.pop_back().unwrap();
                    entry.size += self.right_total;
                    if depth == 0 {
                        break;
                    }
                }
            }
        }
    }

    fn get_top(&self) -> PrintFrame {
        *self.print_stack.last().unwrap_or(&PrintFrame::Broken {
            indent: 0,
            breaks: Breaks::Inconsistent,
        })
    }

    fn print_begin(&mut self, token: BeginToken, size: isize) {
        if size > self.space {
            self.print_stack.push(PrintFrame::Broken {
                indent: self.indent,
                breaks: token.breaks,
            });
            self.indent = match token.indent {
                IndentStyle::Block { offset } => {
                    usize::try_from(self.indent as isize + offset).unwrap()
                }
                IndentStyle::Visual => (MARGIN - self.space) as usize,
            };
        } else {
            self.print_stack.push(PrintFrame::Fits);
        }
    }

    fn print_end(&mut self) {
        if let PrintFrame::Broken { indent, .. } = self.print_stack.pop().unwrap() {
            self.indent = indent;
        }
    }

    fn print_break(&mut self, token: BreakToken, size: isize) {
        let fits = match self.get_top() {
            PrintFrame::Fits => true,
            PrintFrame::Broken {
                breaks: Breaks::Consistent,
                ..
            } => false,
            PrintFrame::Broken {
                breaks: Breaks::Inconsistent,
                ..
            } => size <= self.space,
        };
        if fits {
            self.pending_indentation += token.blank_space;
            self.space -= token.blank_space;
        } else {
            if let Some(pre_break) = token.pre_break {
                self.out.push(pre_break);
            }
            self.out.push('\n');
            let indent = self.indent as isize + token.offset;
            self.pending_indentation = indent;
            self.space = std::cmp::max(MARGIN - indent, MIN_SPACE);
        }
    }

    fn print_string(&mut self, string: &str) {
        self.out.reserve(self.pending_indentation as usize);
        self.out
            .extend(std::iter::repeat_n(' ', self.pending_indentation as usize));
        self.pending_indentation = 0;
        self.out.push_str(string);
        self.space -= string.len() as isize;
    }

    /// "raw box"
    pub fn rbox(&mut self, indent: isize, breaks: Breaks) {
        self.scan_begin(BeginToken {
            indent: IndentStyle::Block { offset: indent },
            breaks,
        })
    }

    /// Inconsistent breaking box
    pub fn ibox(&mut self, indent: isize) {
        self.rbox(indent, Breaks::Inconsistent)
    }

    /// Consistent breaking box
    pub fn cbox(&mut self, indent: isize) {
        self.rbox(indent, Breaks::Consistent)
    }

    pub fn visual_align(&mut self) {
        self.scan_begin(BeginToken {
            indent: IndentStyle::Visual,
            breaks: Breaks::Consistent,
        });
    }

    pub fn break_offset(&mut self, n: usize, off: isize) {
        self.scan_break(BreakToken {
            offset: off,
            blank_space: n as isize,
            ..BreakToken::default()
        });
    }

    pub fn end(&mut self) {
        self.scan_end()
    }

    pub fn eof(mut self) -> String {
        self.scan_eof();
        self.out
    }

    pub fn word<S: Into<Cow<'static, str>>>(&mut self, wrd: S) {
        let string = wrd.into();
        self.scan_string(string)
    }

    fn spaces(&mut self, n: usize) {
        self.break_offset(n, 0)
    }

    pub fn zerobreak(&mut self) {
        self.spaces(0)
    }

    pub fn space(&mut self) {
        self.spaces(1)
    }

    pub fn hardbreak(&mut self) {
        self.spaces(SIZE_INFINITY as usize)
    }

    pub fn is_beginning_of_line(&self) -> bool {
        match self.last_token() {
            Some(last_token) => last_token.is_hardbreak_tok(),
            None => true,
        }
    }

    fn hardbreak_tok_offset(off: isize) -> Token {
        Token::Break(BreakToken {
            offset: off,
            blank_space: SIZE_INFINITY,
            ..BreakToken::default()
        })
    }

    pub fn trailing_comma(&mut self) {
        self.scan_break(BreakToken {
            pre_break: Some(','),
            ..BreakToken::default()
        });
    }

    pub fn trailing_comma_or_space(&mut self) {
        self.scan_break(BreakToken {
            blank_space: 1,
            pre_break: Some(','),
            ..BreakToken::default()
        });
    }

    pub fn word_space<W: Into<Cow<'static, str>>>(&mut self, w: W) {
        self.word(w);
        self.space();
    }

    pub fn popen(&mut self) {
        self.word("(");
    }

    pub fn pclose(&mut self) {
        self.word(")");
    }

    pub fn hardbreak_if_not_bol(&mut self) {
        if !self.is_beginning_of_line() {
            self.hardbreak()
        }
    }

    pub fn space_if_not_bol(&mut self) {
        if !self.is_beginning_of_line() {
            self.space();
        }
    }

    pub fn nbsp(&mut self) {
        self.word(" ")
    }

    pub fn word_nbsp<S: Into<Cow<'static, str>>>(&mut self, w: S) {
        self.word(w);
        self.nbsp()
    }

    pub fn synth_comment(&mut self, text: impl Into<Cow<'static, str>>) {
        self.word("--");
        self.space();
        self.word(text);
    }

    pub fn break_offset_if_not_bol(&mut self, n: usize, off: isize) {
        if !self.is_beginning_of_line() {
            self.break_offset(n, off);
        } else if off != 0 {
            if let Some(last_token) = self.last_token_still_buffered() {
                if last_token.is_hardbreak_tok() {
                    self.replace_last_token_still_buffered(Printer::hardbreak_tok_offset(off));
                }
            }
        }
    }
}

pub trait PrintState: Deref<Target = Printer> + DerefMut {
    fn strsep<T, F>(
        &mut self,
        sep: &'static str,
        space_before: bool,
        breaks: Breaks,
        elems: &[T],
        mut f: F,
    ) where
        F: FnMut(&mut Self, &T),
    {
        self.rbox(0, breaks);
        if let Some((first, rest)) = elems.split_first() {
            f(self, first);
            for elem in rest {
                if space_before {
                    self.space();
                }
                self.word_space(sep);
                f(self, elem);
            }
        }
        self.end();
    }
}

pub trait Enclose: Sized + PartialOrd {
    fn enclose<S, T, F>(
        &self,
        limit: Self,
        lhs: &'static str,
        rhs: &'static str,
        state: &mut S,
        t: &T,
        mut f: F,
    ) where
        S: PrintState,
        F: FnMut(&mut S, &T),
    {
        if *self >= limit {
            state.word(lhs);
            f(state, t);
            state.word(rhs);
        } else {
            f(state, t);
        }
    }
}

impl<P> Enclose for P where P: PartialOrd {}
