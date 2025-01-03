use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};

pub use log::*;

static LOGGER: Logger = Logger;
static BLOCK_LEVEL: AtomicUsize = AtomicUsize::new(0);

pub fn init(trace: bool) -> Result<(), log::SetLoggerError> {
    #[cfg(debug_assertions)]
    let max_level = if trace {
        log::LevelFilter::Trace
    } else {
        log::LevelFilter::Info
    };

    #[cfg(not(debug_assertions))]
    let max_level = log::LevelFilter::Off;

    log::set_logger(&LOGGER).map(|()| log::set_max_level(max_level))
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

struct Logger;

impl log::Log for Logger {
    fn enabled(&self, metadata: &log::Metadata) -> bool {
        metadata.level() <= Level::Trace
    }

    fn log(&self, record: &log::Record) {
        if self.enabled(record.metadata()) {
            let block_level = BLOCK_LEVEL.load(SeqCst);
            println!("{}{}", " ".repeat(block_level), record.args());
        }
    }

    fn flush(&self) {}
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
