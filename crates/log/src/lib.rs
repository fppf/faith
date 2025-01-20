use std::{
    cell::{Cell, RefCell},
    fmt,
    str::FromStr,
    sync::atomic::{AtomicUsize, Ordering::SeqCst},
};

thread_local! {
    static LOGGER: RefCell<Logger> = RefCell::default();
    static MAX_LEVEL: Cell<Level> = const { Cell::new(Level::Warn) };
}

static BLOCK_LEVEL: AtomicUsize = AtomicUsize::new(0);

fn with_logger<F, R>(f: F) -> R
where
    F: FnOnce(&mut Logger) -> R,
{
    LOGGER.with(|l| f(&mut l.borrow_mut()))
}

pub fn init(level: Level) {
    MAX_LEVEL.set(level);
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

pub struct ParseLevelError;

impl FromStr for Level {
    type Err = ParseLevelError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.eq_ignore_ascii_case("error") {
            Ok(Level::Error)
        } else if s.eq_ignore_ascii_case("warn") {
            Ok(Level::Warn)
        } else if s.eq_ignore_ascii_case("info") {
            Ok(Level::Info)
        } else if s.eq_ignore_ascii_case("debug") {
            Ok(Level::Debug)
        } else if s.eq_ignore_ascii_case("trace") {
            Ok(Level::Trace)
        } else {
            Err(ParseLevelError)
        }
    }
}

pub fn block_log<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    block_in();
    let res = f();
    block_out();
    res
}

pub fn block_in() {
    BLOCK_LEVEL.fetch_add(2, SeqCst);
}

pub fn block_out() {
    BLOCK_LEVEL.fetch_sub(2, SeqCst);
}

#[derive(Default)]
struct Logger {
    #[cfg(debug_assertions)]
    buffer: String,
}

impl Logger {
    fn log(&mut self, args: fmt::Arguments<'_>) {
        let block_level = BLOCK_LEVEL.load(SeqCst);
        let msg = format!("{}{}", " ".repeat(block_level), args);
        println!("{msg}");

        #[cfg(debug_assertions)]
        self.buffer.push_str(&msg);
    }
}

#[cfg(debug_assertions)]
pub fn get_buffer() -> String {
    with_logger(|l| l.buffer.clone())
}

pub fn log(level: Level, args: fmt::Arguments<'_>) {
    if level <= MAX_LEVEL.get() {
        with_logger(|l| l.log(args));
    }
}

#[macro_export]
macro_rules! log {
    ($level:expr, $($arg:tt)+) => {
        $crate::log($level, format_args!($($arg)+));
    };
}

#[macro_export]
macro_rules! error {
    ($($arg:tt)+) => {
        $crate::log!($crate::Level::Error, $($arg)+);
    };
}

#[macro_export]
macro_rules! warn {
    ($($arg:tt)+) => {
        $crate::log!($crate::Level::Warn, $($arg)+);
    };
}

#[macro_export]
macro_rules! info {
    ($($arg:tt)+) => {
        $crate::log!($crate::Level::Info, $($arg)+);
    };
}

#[macro_export]
macro_rules! debug {
    ($($arg:tt)+) => {
        $crate::log!($crate::Level::Debug, $($arg)+);
    };
}

#[macro_export]
macro_rules! trace {
    ($($arg:tt)+) => {
        $crate::log!($crate::Level::Trace, $($arg)+);
    };
}

#[macro_export]
macro_rules! block {
    ($e:expr) => {
        if cfg!(debug_assertions) {
            $crate::block_log(|| $e)
        } else {
            $e
        }
    };
    ($target:expr, $e:expr) => {
        if cfg!(debug_assertions) {
            log::trace!($target);
            $crate::block_log(|| $e)
        } else {
            $e
        }
    };
}
