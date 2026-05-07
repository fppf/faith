use std::{env, path::PathBuf};

use driver::{Level, Mode, Options, Source};
use lexopt::{Arg, ValueExt};

fn main() {
    let args = parse_args();

    if driver::run(Source::File(args.program_path), &args.options) {
        std::process::exit(1);
    }
}

struct Args {
    program_path: PathBuf,
    options: Options,
}

fn parse_args() -> Args {
    let mut parser = lexopt::Parser::from_env();
    let binary_name = parser.bin_name().unwrap_or("faithc");
    let help_message = format!("usage: {binary_name} FILE.fe [--no-std] [--dump-mir]");

    parse_args_with(&mut parser, &help_message).unwrap_or_else(|e| {
        eprintln!("argument parsing error: {e}");
        eprintln!("{help_message}");
        std::process::exit(1);
    })
}

fn parse_args_with(parser: &mut lexopt::Parser, help_message: &str) -> Result<Args, lexopt::Error> {
    let log_level = match env::var("FAITH_LOG") {
        Ok(s) => s.parse().unwrap_or(Level::Warn),
        Err(_) => Level::Warn,
    };

    let mut program_path = None;
    let mut options = Options {
        include_std: true,
        parse_only: false,
        dump_ast: false,
        dump_hir: false,
        dump_mir: false,
        mode: Mode::Real(log_level),
    };

    while let Some(arg) = parser.next()? {
        match arg {
            Arg::Value(val) if program_path.is_none() => {
                program_path = Some(PathBuf::from(val.string()?));
            }
            Arg::Long("test") => options.mode = Mode::Test,
            Arg::Long("no-std") => options.include_std = false,
            Arg::Long("parse-only") => options.parse_only = true,
            Arg::Long("dump-ast") => options.dump_ast = true,
            Arg::Long("dump-hir") => options.dump_hir = true,
            Arg::Long("dump-mir") => options.dump_mir = true,
            Arg::Short('h') | Arg::Long("help") => {
                println!("{help_message}");
                std::process::exit(0);
            }
            _ => return Err(arg.unexpected()),
        }
    }

    let program_path = program_path.ok_or("missing program path argument")?;
    Ok(Args {
        program_path,
        options,
    })
}
