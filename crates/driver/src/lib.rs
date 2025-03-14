use std::path::PathBuf;

use span::diag;

#[derive(PartialEq)]
pub enum Pass {
    Parse,
    Infer,
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
    let syntax_arena = syntax::Arena::default();
    let program = match src {
        Source::File(path) => syntax::parse_program_in(&syntax_arena, &path),
        Source::Str(src) => syntax::parse_str_program_in(&syntax_arena, &src),
    }?;

    if stop_after == Pass::Parse {
        return Ok(());
    }

    let ctxt = infer::ty::TyCtxt::default();
    infer::infer_program_in(&ctxt, program)?;

    if stop_after == Pass::Infer {
        return Ok(());
    }

    Ok(())
}
