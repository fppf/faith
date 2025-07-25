pub mod ast;

mod grammar;
mod lexer;
mod parser;
mod pretty;
mod token;

use ast::AstId;
use lexer::Lexer;
use parser::Parser;
use span::diag::{Diagnostic, Level};

base::declare_arena!('ast, [
    program: ast::Program<'ast>,
]);

pub fn parse_program_in<'ast>(
    arena: &'ast Arena<'ast>,
    path: &std::path::Path,
    should_parse_std: bool,
) -> Result<&'ast ast::Program<'ast>, Diagnostic> {
    let parser = make_parser(arena, PathOrStr::Path(path), should_parse_std, AstId::ZERO)?;
    grammar::program(parser).map_err(Diagnostic::from)
}

pub fn parse_str_program_in<'ast>(
    arena: &'ast Arena<'ast>,
    src: &str,
    should_parse_std: bool,
) -> Result<&'ast ast::Program<'ast>, Diagnostic> {
    let parser = make_parser(arena, PathOrStr::Str(src), should_parse_std, AstId::ZERO)?;
    grammar::program(parser).map_err(Diagnostic::from)
}

pub(crate) enum PathOrStr<'a> {
    Path(&'a std::path::Path),
    Str(&'a str),
}

pub(crate) fn make_parser<'ast>(
    arena: &'ast Arena<'ast>,
    source: PathOrStr<'_>,
    should_parse_std: bool,
    ast_id: AstId,
) -> Result<Parser<'ast>, Diagnostic> {
    span::with_source_map(|sm| {
        let source_id = match source {
            PathOrStr::Path(path) => {
                path_check(path)?;
                sm.load_file(path).map_err(map_load_error)?
            }
            PathOrStr::Str(s) => sm.load_str(s),
        };
        Ok(Parser::new(
            arena,
            source_id,
            ast_id,
            should_parse_std,
            Lexer::new(&sm[source_id]),
        ))
    })
}

fn path_check(path: &std::path::Path) -> Result<(), Diagnostic> {
    match path.extension() {
        Some(ext) if ext != span::SRC_EXT => {
            Err(Diagnostic::new(Level::Error).with_message(format!(
                "file '{}' has extension '{}'; please rename to '{}'",
                path.display(),
                ext.to_string_lossy(),
                path.with_extension(span::SRC_EXT).display(),
            )))
        }
        Some(_) => Ok(()),
        None => Err(Diagnostic::new(Level::Error).with_message(format!(
            "file '{}' has no extension; please rename to '{}'",
            path.display(),
            path.with_extension(span::SRC_EXT).display(),
        ))),
    }
}

pub(crate) fn map_load_error(e: span::LoadError) -> Diagnostic {
    Diagnostic::new(Level::Error).with_message(format!(
        "could not load file '{}': {}",
        e.path.display(),
        e.err
    ))
}
