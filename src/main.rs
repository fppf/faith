use std::{
    env,
    path::{Path, PathBuf},
};

use span::diag;

fn main() {
    log::init(true).unwrap();
    let args: Vec<_> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} FILE.fth", args[0]);
        std::process::exit(1);
    }

    let program_path = PathBuf::from(&args[1]);
    match run_passes(&program_path) {
        Ok(()) => (),
        Err(e) => diag::emit(e),
    }

    if diag::report() {
        std::process::exit(1);
    }
}

fn run_passes(path: &Path) -> Result<(), diag::Diagnostic> {
    let hir_arena = hir::Arena::default();
    let hir = hir::parse_and_lower_program_in(&hir_arena, path)?;

    println!("{:#?}", hir);
    let _data = infer::infer_program_in(&hir_arena, hir)?;

    //for (e, t) in data.expr_types {
    //    log::trace!("{e} : {t}");
    //}

    //let mdl = mir::lower(&hir_arena, data, hir);
    //log::info!(target: "MIR", "\n{mdl}");
    Ok(())
}
