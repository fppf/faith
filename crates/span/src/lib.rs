//! Source file and span management.
//!
//! Modeled after `rustc_span`.
use std::{
    cell::RefCell,
    fmt, fs, io,
    ops::{Add, Deref, DerefMut, Index, Range, Sub},
    path::{Path, PathBuf},
    rc::Rc,
};

use codespan_reporting::files;

use base::{hash::Map, index::IndexVec};

mod intern;

pub mod diag;

pub use intern::{Ident, Sym};

pub const SRC_EXT: &str = "fth";

thread_local! {
    /// The global source map.
    static SOURCE_MAP: RefCell<SourceMap> = RefCell::default();
}

pub fn with_source_map<F, R>(f: F) -> R
where
    F: FnOnce(&mut SourceMap) -> R,
{
    SOURCE_MAP.with(|x| f(&mut x.borrow_mut()))
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub start: BytePos,
    pub end: BytePos,
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start.to_u32(), self.end.to_u32())
    }
}

impl From<Range<usize>> for Span {
    fn from(range: Range<usize>) -> Self {
        Self::new(
            BytePos::from_usize(range.start),
            BytePos::from_usize(range.end),
        )
    }
}

impl Span {
    #[inline(always)]
    pub fn new(start: BytePos, end: BytePos) -> Self {
        debug_assert!(start <= end);
        Self { start, end }
    }

    #[inline]
    pub fn dummy() -> Self {
        Self::from(0..0)
    }

    #[inline]
    pub fn merge(&self, sp: Self) -> Self {
        if self.start <= sp.end {
            Self::new(self.start, sp.end)
        } else {
            *self
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Sp<T> {
    pub value: T,
    pub span: Span,
}

impl<T> Sp<T> {
    #[inline]
    pub fn new(value: T, span: Span) -> Self {
        Self { value, span }
    }

    #[inline]
    pub fn span(&self) -> Span {
        self.span
    }

    #[inline]
    pub fn map<F, U>(self, mut f: F) -> Sp<U>
    where
        F: FnMut(T) -> U,
    {
        Sp::new(f(self.value), self.span)
    }
}

impl<T> Deref for Sp<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> DerefMut for Sp<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T: PartialEq> PartialEq for Sp<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T: Eq> Eq for Sp<T> {}

impl<T> From<T> for Sp<T> {
    fn from(t: T) -> Self {
        Sp::new(t, Span::dummy())
    }
}

impl<T> fmt::Display for Sp<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct BytePos(u32);

impl BytePos {
    #[inline(always)]
    pub fn from_usize(n: usize) -> Self {
        Self(n as u32)
    }

    #[inline(always)]
    pub fn to_usize(self) -> usize {
        self.0 as usize
    }

    #[inline(always)]
    pub fn from_u32(n: u32) -> Self {
        Self(n)
    }

    #[inline(always)]
    pub fn to_u32(self) -> u32 {
        self.0
    }
}

impl Add for BytePos {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Sub for BytePos {
    type Output = Self;

    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0)
    }
}

#[derive(Default)]
pub struct SourceMap {
    used_space: u32,
    files: IndexVec<SourceId, Rc<SourceFile>>,
    path_cache: Map<PathBuf, SourceId>,
}

base::newtype_index! {
    pub struct SourceId {}
}

#[derive(Debug)]
pub struct LoadError {
    pub path: PathBuf,
    pub err: io::Error,
}

impl SourceMap {
    pub fn load_file(&mut self, path: &Path) -> Result<SourceId, LoadError> {
        let path = path.with_extension(SRC_EXT);
        let path = path.canonicalize().map_err(|err| LoadError {
            path: path.clone(),
            err,
        })?;
        log::info!("loading file '{}'", path.display());
        let src = fs::read_to_string(&path).map_err(|err| LoadError {
            path: path.clone(),
            err,
        })?;
        Ok(self.load(src, Some(&path)))
    }

    pub fn load_str(&mut self, src: &str) -> SourceId {
        self.load(src, None)
    }

    fn load<S>(&mut self, src: S, path: Option<&Path>) -> SourceId
    where
        S: Into<String>,
    {
        if let Some(path) = path {
            if let Some(source_id) = self.lookup_existing_source_id(path) {
                return source_id;
            }
        }

        let src = src.into();
        let len = src.len();
        let start = self.alloc_space(len);
        let line_starts: Vec<_> = files::line_starts(&src).collect();
        let source_file = SourceFile {
            path: path.map(Path::to_path_buf),
            src,
            start: BytePos::from_usize(start),
            end: BytePos::from_usize(start + len),
            line_starts,
        };
        let source_id = self.files.push(Rc::new(source_file));
        if let Some(path) = path {
            self.path_cache.insert(path.to_path_buf(), source_id);
        }
        source_id
    }

    pub fn lookup_existing_source_id(&self, path: &Path) -> Option<SourceId> {
        let path = path.with_extension(SRC_EXT).canonicalize().ok()?;
        self.path_cache.get(&path).copied()
    }

    pub fn lookup_source_file(&self, pos: BytePos) -> Rc<SourceFile> {
        self.files[self.lookup_source_file_idx(pos)].clone()
    }

    pub fn lookup_source_file_idx(&self, pos: BytePos) -> SourceId {
        self.files
            .raw
            .binary_search_by_key(&pos, |key| key.start)
            .unwrap_or_else(|i| i - 1)
            .into()
    }

    fn alloc_space(&mut self, size: usize) -> usize {
        assert!(size < u32::MAX as usize, "Source file exceeded 4GB");
        let size = size as u32;
        let current = self.used_space;
        let next = current
            .checked_add(size)
            .and_then(|next| next.checked_add(1))
            .unwrap();
        self.used_space = next;
        current as usize
    }
}

impl Index<SourceId> for SourceMap {
    type Output = Rc<SourceFile>;

    fn index(&self, index: SourceId) -> &Self::Output {
        &self.files[index]
    }
}

pub struct SourceFile {
    pub path: Option<PathBuf>,
    pub src: String,
    pub start: BytePos,
    pub end: BytePos,
    line_starts: Vec<usize>,
}

impl SourceFile {
    pub fn path(&self) -> &str {
        match &self.path {
            Some(path) => path.to_str().unwrap(),
            None => "",
        }
    }

    fn line_start(&self, line_index: usize) -> Result<usize, files::Error> {
        use std::cmp::Ordering;

        match line_index.cmp(&self.line_starts.len()) {
            Ordering::Less => Ok(self.line_starts[line_index]),
            Ordering::Equal => Ok(self.src.len()),
            Ordering::Greater => Err(files::Error::LineTooLarge {
                given: line_index,
                max: self.line_starts.len() - 1,
            }),
        }
    }
}

impl<'a> files::Files<'a> for SourceMap {
    type FileId = SourceId;
    type Name = &'a str;
    type Source = &'a str;

    fn name(&'a self, id: Self::FileId) -> Result<Self::Name, files::Error> {
        Ok(self[id].path())
    }

    fn source(&'a self, id: Self::FileId) -> Result<Self::Source, files::Error> {
        Ok(&self[id].src)
    }

    fn line_index(&'a self, id: Self::FileId, byte_index: usize) -> Result<usize, files::Error> {
        self[id]
            .line_starts
            .binary_search(&byte_index)
            .or_else(|next_line| Ok(next_line - 1))
    }

    fn line_range(
        &'a self,
        id: Self::FileId,
        line_index: usize,
    ) -> Result<Range<usize>, files::Error> {
        let line_start = self[id].line_start(line_index)?;
        let next_line_start = self[id].line_start(line_index + 1)?;
        Ok(line_start..next_line_start)
    }
}
