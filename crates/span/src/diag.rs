use std::{cell::RefCell, io};

use codespan_reporting::{
    diagnostic::{self, Severity},
    term::{
        emit as term_emit,
        termcolor::{ColorChoice, ColorSpec, NoColor, StandardStream, WriteColor},
        Config,
    },
};

use crate::{BytePos, SourceId, SourceMap, Span};

thread_local! {
    /// The global diagnostic store.
    static DIAGNOSTIC_STORE: RefCell<DiagnosticStore> = RefCell::new(DiagnosticStore::default());
}

fn with_diagnostic_store<F, R>(f: F) -> R
where
    F: FnOnce(&mut DiagnosticStore) -> R,
{
    DIAGNOSTIC_STORE.with(|x| f(&mut x.borrow_mut()))
}

pub fn emit<D>(diag: D)
where
    D: Into<Diagnostic>,
{
    with_diagnostic_store(|store| store.diags.push(diag.into()));
}

enum ReportWriter {
    Test(NoColor<Vec<u8>>),
    Real(StandardStream),
}

impl io::Write for ReportWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            Self::Test(w) => w.write(buf),
            Self::Real(w) => w.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Test(w) => w.flush(),
            Self::Real(w) => w.flush(),
        }
    }
}

impl WriteColor for ReportWriter {
    fn supports_color(&self) -> bool {
        match self {
            Self::Test(w) => w.supports_color(),
            Self::Real(w) => w.supports_color(),
        }
    }

    fn set_color(&mut self, spec: &ColorSpec) -> std::io::Result<()> {
        match self {
            Self::Test(w) => w.set_color(spec),
            Self::Real(w) => w.set_color(spec),
        }
    }

    fn reset(&mut self) -> std::io::Result<()> {
        match self {
            Self::Test(w) => w.reset(),
            Self::Real(w) => w.reset(),
        }
    }
}

pub fn report(test: bool) -> bool {
    let config = Config::default();

    let mut w = if test {
        ReportWriter::Test(NoColor::new(Vec::new()))
    } else {
        ReportWriter::Real(StandardStream::stderr(ColorChoice::Always))
    };

    with_diagnostic_store(|store| {
        if store.diags.iter().any(Diagnostic::is_error) {
            crate::with_source_map(|sm| {
                for diag in &store.diags {
                    term_emit(&mut w, &config, sm, &convert(sm, diag.clone())).unwrap();
                }
            });

            if let ReportWriter::Test(w) = w {
                log::error!("{}", String::from_utf8_lossy(&w.into_inner()));
            }

            true
        } else {
            false
        }
    })
}

#[derive(Default)]
struct DiagnosticStore {
    diags: Vec<Diagnostic>,
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
    level: Level,
    message: String,
    labels: Vec<Label>,
}

#[derive(Clone, Debug)]
pub struct Label {
    span: Span,
    message: String,
    is_primary: bool,
}

impl Label {
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
            is_primary: false,
        }
    }

    pub fn primary(mut self) -> Self {
        self.is_primary = true;
        self
    }
}

impl Diagnostic {
    pub fn new(level: Level) -> Self {
        Self {
            level,
            message: String::new(),
            labels: Vec::new(),
        }
    }

    pub fn with_message(mut self, message: impl Into<String>) -> Self {
        self.message = message.into();
        self
    }

    pub fn with_labels(mut self, mut labels: Vec<Label>) -> Self {
        self.labels.append(&mut labels);
        self
    }

    fn is_error(&self) -> bool {
        self.level == Level::Error
    }
}

fn convert(sm: &SourceMap, diag: Diagnostic) -> diagnostic::Diagnostic<SourceId> {
    diagnostic::Diagnostic::new(diag.level.into())
        .with_message(diag.message)
        .with_labels(
            diag.labels
                .into_iter()
                .map(|label| convert_label(sm, label))
                .collect(),
        )
}

fn convert_label(sm: &SourceMap, label: Label) -> diagnostic::Label<SourceId> {
    let source_id = sm.lookup_source_file_idx(label.span.start);
    let sf = &sm[source_id];
    let span = fix_eof_hack(label.span, sf.start, sf.end);
    diagnostic::Label::new(
        if label.is_primary {
            diagnostic::LabelStyle::Primary
        } else {
            diagnostic::LabelStyle::Secondary
        },
        source_id,
        (span.start - sf.start).to_usize()..(span.end - sf.start).to_usize(),
    )
    .with_message(label.message)
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Level {
    Error,
    Warn,
    Note,
    Help,
}

impl From<Level> for Severity {
    fn from(level: Level) -> Self {
        match level {
            Level::Error => Self::Error,
            Level::Warn => Self::Warning,
            Level::Note => Self::Note,
            Level::Help => Self::Help,
        }
    }
}

// TODO. we shouldn't create spans that don't index properly into a sourcefile.
fn fix_eof_hack(span: Span, start: BytePos, end: BytePos) -> Span {
    if span.end >= end {
        Span::new(start, end - BytePos::from_usize(1))
    } else {
        span
    }
}
