use std::{env, path::PathBuf};

use driver::{Level, Mode, Pass, Source};

fn main() {
    let args: Vec<_> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} FILE.fth", args[0]);
        std::process::exit(1);
    }

    let log_level = match env::var("FAITH_LOG") {
        Ok(s) => s.parse().unwrap_or(Level::Warn),
        Err(_) => Level::Warn,
    };

    let program_path = PathBuf::from(&args[1]);
    if driver::run(
        Source::File(program_path),
        Mode::Real(log_level),
        Pass::Infer,
    ) {
        std::process::exit(1);
    }
}
