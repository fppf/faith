use std::path::PathBuf;

use base::pp::{DocArena, PRETTY_WIDTH};
use span::diag;

#[derive(PartialEq)]
pub enum Pass {
    Parse,
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

pub fn run(src: Source, mode: Mode, should_parse_std: bool, stop_after: Pass) -> bool {
    match mode {
        Mode::Test => log::init(Level::Trace),
        Mode::Real(lvl) => log::init(lvl),
    };

    match run_passes(src, should_parse_std, stop_after) {
        Ok(()) => (),
        Err(e) => diag::emit(e),
    }

    diag::report(mode == Mode::Test)
}

fn run_passes(
    src: Source,
    should_parse_std: bool,
    stop_after: Pass,
) -> Result<(), diag::Diagnostic> {
    let syntax_arena = syntax::Arena::default();
    let program = match src {
        Source::File(path) => syntax::parse_program_in(&syntax_arena, &path, should_parse_std),
        Source::Str(src) => syntax::parse_str_program_in(&syntax_arena, &src, should_parse_std),
    }?;

    if stop_after == Pass::Parse {
        return Ok(());
    }

    let ty_arena = infer::ty::Arena::default();
    let ctxt = infer::ty::TyCtxt::new(&ty_arena);
    let mut hir = infer::infer_program_in(&ctxt, program)?;

    if stop_after == Pass::Infer {
        return Ok(());
    }

    infer::match_compile::compile(&ctxt, &mut hir)?;

    let mir = mir::lower(&ctxt, &hir);
    let doc_arena = DocArena::default();
    println!("{}", mir.to_doc(&doc_arena).pretty_string(PRETTY_WIDTH));

    Ok(())
}
