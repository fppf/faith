use std::{env, path::PathBuf};

use driver::{Level, Mode, Pass, Source};

fn main() {
    let args: Vec<_> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: {} FILE.fe [--no-std]", args[0]);
        std::process::exit(1);
    }

    let log_level = match env::var("FAITH_LOG") {
        Ok(s) => s.parse().unwrap_or(Level::Warn),
        Err(_) => Level::Warn,
    };

    let program_path = PathBuf::from(&args[1]);
    let mut should_parse_std = true;
    if let Some(arg) = args.get(2)
        && arg == "--no-std"
    {
        should_parse_std = false;
    }
    if driver::run(
        Source::File(program_path),
        Mode::Real(log_level),
        should_parse_std,
        Pass::Mir,
    ) {
        std::process::exit(1);
    }
}
