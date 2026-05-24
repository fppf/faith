use std::{
    env,
    error::Error,
    fs,
    path::PathBuf,
    process::{self, Command},
};

use similar::TextDiff;
use walkdir::WalkDir;

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = env::args().collect();
    if args.len() < 3 {
        eprintln!(
            "usage {} compiler_cli_binary test_directory_root",
            env::current_exe()?.display()
        );
        process::exit(1);
    }

    let command = PathBuf::from(&args[1]);
    let test_dir = PathBuf::from(&args[2]);
    println!("Running tests in {}", test_dir.display());

    for entry in WalkDir::new(test_dir) {
        let entry = entry?;
        let test_path = entry.path();

        // Tests are .fe source files only.
        if test_path.is_dir() || test_path.extension().is_some_and(|ext| ext != "fe") {
            continue;
        }

        let contents = fs::read_to_string(test_path)?;

        let mut args = Vec::new();
        let mut found_expected = false;
        let mut expected = String::new();
        for line in contents.lines() {
            if found_expected {
                if let Some(line) = line.strip_prefix("-- ") {
                    expected.push_str(line);
                    expected.push('\n');
                }
            } else if line.starts_with("-- args:") {
                for arg in line.split_whitespace().skip(2) {
                    args.push(arg);
                }
                found_expected = true;
            }
        }
        let expected = expected.trim_ascii();

        println!("[Running {} {}]", test_path.display(), args.join(" "));

        let output = Command::new(&command).arg(test_path).args(args).output()?;

        let output = str::from_utf8(if expected.contains("error:") {
            &output.stderr
        } else {
            &output.stdout
        })?;
        let output = output.trim_ascii();

        let diff = TextDiff::from_lines(expected, output);
        print!(
            "{}",
            diff.unified_diff()
                .header("expected", "output")
                .missing_newline_hint(false)
        );
    }

    Ok(())
}
