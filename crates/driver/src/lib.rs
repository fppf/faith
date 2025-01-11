use std::path::PathBuf;

use log::Level;
use span::diag;

#[derive(PartialEq)]
pub enum Pass {
    Parse,
    Lower,
    Infer,
}

pub enum Source {
    Str(String),
    File(PathBuf),
}

#[derive(PartialEq)]
pub enum Mode {
    Test,
    Real,
}

pub use log::get_buffer;

pub fn run(src: Source, mode: Mode, stop_after: Pass) {
    match mode {
        Mode::Test => log::init(Level::Trace),
        Mode::Real => log::init(Level::Warn),
    };

    match run_passes(src, stop_after) {
        Ok(()) => (),
        Err(e) => diag::emit(e),
    }

    if diag::report(mode == Mode::Test) {
        std::process::exit(1);
    }
}

fn run_passes(src: Source, stop_after: Pass) -> Result<(), diag::Diagnostic> {
    let hir_arena = hir::Arena::default();
    let hir = match src {
        Source::File(path) => hir::parse_and_lower_program_in(&hir_arena, &path),
        Source::Str(src) => hir::parse_and_lower_str_program_in(&hir_arena, &src),
    }?;

    if stop_after == Pass::Lower {
        return Ok(());
    }

    let _ = infer::infer_program_in(&hir_arena, hir)?;

    if stop_after == Pass::Infer {
        return Ok(());
    }

    Ok(())
}
