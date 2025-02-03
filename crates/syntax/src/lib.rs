#![feature(let_chains)]
pub mod ast;

mod grammar;
mod lexer;
mod parser;
mod pretty;
mod token;

use lexer::Lexer;
use parser::Parser;
use span::{
    Ident, Sp, Span, Sym,
    diag::{Diagnostic, Level},
};

// An ephemeral AST arena, constructed to parse a single compilation unit
// on demand and dropped after the AST fragment is lowered to HIR.
base::declare_arena!('ast, []);

pub fn parse_program_in<'ast>(
    arena: &'ast Arena<'ast>,
    path: &std::path::Path,
) -> Result<&'ast ast::Program<'ast>, Diagnostic> {
    path_check(path)?;
    span::with_source_map(|sm| {
        let source_id = sm.load_file(path).map_err(map_load_error)?;
        let mut parser = Parser::new(arena, Lexer::new(&sm[source_id]));
        grammar::program(source_id, &mut parser).map_err(Diagnostic::from)
    })
}

pub fn parse_comp_unit_in<'ast>(
    arena: &'ast Arena<'ast>,
    path: &std::path::Path,
) -> Result<&'ast ast::CompUnit<'ast>, Diagnostic> {
    path_check(path)?;
    span::with_source_map(|sm| {
        let source_id = sm.load_file(path).map_err(map_load_error)?;
        let mut parser = Parser::new(arena, Lexer::new(&sm[source_id]));
        grammar::comp_unit(source_id, &mut parser).map_err(Diagnostic::from)
    })
}

pub fn parse_str_program_in<'ast>(
    arena: &'ast Arena<'ast>,
    src: &str,
) -> Result<&'ast ast::Program<'ast>, Diagnostic> {
    span::with_source_map(|sm| {
        let source_id = sm.load_str(src);
        let mut parser = Parser::new(arena, Lexer::new(&sm[source_id]));
        grammar::program(source_id, &mut parser).map_err(Diagnostic::from)
    })
}

pub fn std_import<'ast>(arena: &'ast Arena<'ast>) -> Result<&'ast Sp<ast::Item<'ast>>, Diagnostic> {
    let mod_ident = Ident::new(Sym::intern("std"), Span::dummy());
    let import_path =
        std::path::Path::new(&std::env::var("FAITH_STD").unwrap_or("./lib".into())).join("std.fth");
    let import_path = arena.alloc_str(&import_path.to_string_lossy());
    let import_path = arena.alloc(std::path::Path::new(import_path));

    if !import_path.exists() {
        println!("here");
        return Err(Diagnostic::new(Level::Warn).with_message(format!(
            "cannot find standard library at '{}'",
            import_path.display()
        )));
    }

    let import_item = arena.alloc(Sp::new(
        ast::Item::Mod(
            mod_ident,
            arena.alloc(Sp::new(ast::ModExpr::Import(import_path), Span::dummy())),
        ),
        Span::dummy(),
    ));
    Ok(import_item)
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

fn map_load_error(e: span::LoadError) -> Diagnostic {
    Diagnostic::new(Level::Error).with_message(format!(
        "could not load file '{}': {}",
        e.path.display(),
        e.err
    ))
}
