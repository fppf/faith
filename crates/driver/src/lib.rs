use std::path::PathBuf;

use span::diag;

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

pub struct Options {
    pub include_std: bool,
    pub parse_only: bool,
    pub dump_ast: bool,
    pub dump_mir: bool,
    pub mode: Mode,
}

pub fn run(src: Source, options: &Options) -> bool {
    match options.mode {
        Mode::Test => log::init(Level::Trace),
        Mode::Real(lvl) => log::init(lvl),
    };

    match run_passes(src, options) {
        Ok(()) => (),
        Err(e) => diag::emit(e),
    }

    diag::report(options.mode == Mode::Test)
}

fn run_passes(src: Source, options: &Options) -> Result<(), diag::Diagnostic> {
    let ctxt = infer::ty::TyCtxt::new();
    let hir = {
        let syntax_arena = syntax::Arena::default();
        let program = match src {
            Source::File(path) => {
                syntax::parse_program_in(&syntax_arena, &path, options.include_std)
            }
            Source::Str(src) => {
                syntax::parse_str_program_in(&syntax_arena, &src, options.include_std)
            }
        }?;

        if options.dump_ast {
            println!("{program}");
        }

        if options.parse_only {
            return Ok(());
        }

        infer::infer_program_in(&ctxt, program)
    }?;

    let _mir = middle::lower_and_transform(&ctxt, &hir);

    Ok(())
}
