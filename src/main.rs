use std::{env, path::PathBuf};

use driver::{Mode, Pass, Source};

fn main() {
    let args: Vec<_> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} FILE.fth", args[0]);
        std::process::exit(1);
    }

    let program_path = PathBuf::from(&args[1]);
    driver::run(Source::File(program_path), Mode::Real, Pass::Infer);
}
