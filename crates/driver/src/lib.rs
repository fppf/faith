use std::path::PathBuf;

use span::diag;

#[derive(PartialEq)]
pub enum Pass {
    Parse,
    Hir,
    Infer,
    Mir,
}

pub enum Source {
    Str(String),
    File(PathBuf),
}

#[derive(PartialEq)]
pub enum Mode {
    Test,
    Real(Level),
}

pub use log::{Level, get_buffer};

pub fn run(src: Source, mode: Mode, stop_after: Pass) -> bool {
    match mode {
        Mode::Test => log::init(Level::Trace),
        Mode::Real(lvl) => log::init(lvl),
    };

    match run_passes(src, stop_after) {
        Ok(()) => (),
        Err(e) => diag::emit(e),
    }

    diag::report(mode == Mode::Test)
}

fn run_passes(src: Source, stop_after: Pass) -> Result<(), diag::Diagnostic> {
    let hir_arena = hir::Arena::default();
    let hir = match src {
        Source::File(path) => hir::parse_and_lower_program_in(&hir_arena, &path),
        Source::Str(src) => hir::parse_and_lower_str_program_in(&hir_arena, &src),
    }?;

    if stop_after == Pass::Hir {
        return Ok(());
    }

    let infer_data = infer::infer_program_in(&hir_arena, hir)?;

    if stop_after == Pass::Infer {
        return Ok(());
    }

    mir::lower(&hir_arena, infer_data, hir);

    Ok(())
}
