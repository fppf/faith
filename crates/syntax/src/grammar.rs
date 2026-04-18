use span::{
    Ident, SourceId, Sp, Span, Sym,
    diag::{Diagnostic, Level},
};

use crate::{
    PathOrStr,
    ast::*,
    make_parser,
    parser::{ParseError, ParseResult, Parser},
    token::{LitToken, TokenKind::*},
};

macro_rules! alloc {
    ($p:ident, $e:expr) => {
        &*$p.arena.alloc($e)
    };
}

macro_rules! alloc_iter {
    ($p:ident, $e:expr) => {
        &*$p.arena.alloc_from_iter($e)
    };
}

pub fn program(mut p: Parser<'_>) -> ParseResult<&Program<'_>> {
    let unit = comp_unit_eof(p.current_comp_unit, &mut p, false)?;
    p.expect(KW_MAIN)?;
    p.expect(EQUAL)?;
    let main = alloc!(p, expr(&mut p)?);
    let m = p.start();
    while p.eat(NEWLINE) {}
    if p.at(EOF) {
        Ok(alloc!(
            p,
            Program {
                unit,
                main,
                imports: p.imports
            }
        ))
    } else {
        while !p.at(EOF) {
            p.bump_any();
        }
        Err(ParseError::new("unexpected input", p.end(m)))
    }
}

pub fn comp_unit<'ast>(
    source_id: SourceId,
    p: &mut Parser<'ast>,
) -> ParseResult<&'ast CompUnit<'ast>> {
    let comp_unit = comp_unit_eof(source_id, p, true)?;
    p.imports.insert(source_id, comp_unit);
    Ok(comp_unit)
}

fn parse_import(
    import_path: &std::path::Path,
    span: Span,
    p: &mut Parser<'_>,
) -> ParseResult<SourceId> {
    let mut file_path = std::path::PathBuf::new();
    if let Some(base_path) = span::with_source_map(|sm| sm[p.current_comp_unit].path.clone()) {
        file_path.push(base_path.parent().unwrap());
    }
    file_path.push(import_path);
    Ok(
        if let Some(source_id) =
            span::with_source_map(|sm| sm.lookup_existing_source_id(&file_path))
        {
            source_id
        } else {
            let mut sub_p = make_parser(
                p.arena,
                PathOrStr::Path(&file_path),
                p.should_parse_std,
                p.ast_id,
            )
            .map_err(|_e /*FIXME*/| {
                ParseError::new(format!("cannot parse {}", file_path.display()), span)
            })?;
            sub_p.inside_std = p.inside_std;
            log::info!("parsing '{}'", import_path.display());
            let comp_unit = comp_unit(sub_p.current_comp_unit, &mut sub_p)?;
            p.imports.extend(sub_p.imports);
            p.ast_id = sub_p.ast_id;
            comp_unit.source_id
        },
    )
}

fn std_import_item<'ast>(p: &mut Parser<'ast>) -> ParseResult<Option<Sp<Item<'ast>>>> {
    let import_path = std::path::Path::new(&std::env::var("FAITH_STD").unwrap_or("./lib".into()))
        .join(format!("std.{}", span::SRC_EXT));
    if !import_path.exists() {
        span::diag::emit(Diagnostic::new(Level::Warn).with_message(format!(
            "cannot find standard library at '{}'",
            import_path.display()
        )));
        return Ok(None);
    }

    p.inside_std = true;
    let source_id = parse_import(&import_path, Span::dummy(), p)?;
    p.inside_std = false;
    Ok(Some(Sp::new(
        Item::Mod(
            Id::new(Ident::new(Sym::intern("std"), Span::dummy()), AstId::ZERO),
            p.arena
                .alloc(Sp::new(ModExpr::Import(source_id), Span::dummy())),
        ),
        Span::dummy(),
    )))
}

fn comp_unit_eof<'ast>(
    source_id: SourceId,
    p: &mut Parser<'ast>,
    eof: bool,
) -> ParseResult<&'ast CompUnit<'ast>> {
    let mut items = Vec::new();
    if p.should_parse_std
        && !p.inside_std
        && let Some(std) = std_import_item(p)?
    {
        items.push(std);
    }
    p.eat(NEWLINE);
    while !p.at(EOF) && !p.at(KW_MAIN) {
        items.push(struct_item(p)?);
    }
    let m = p.start();
    while p.eat(NEWLINE) {}
    if !eof || p.at(EOF) {
        Ok(alloc!(
            p,
            CompUnit {
                source_id,
                items: alloc_iter!(p, items),
            }
        ))
    } else {
        while !p.at(EOF) {
            p.bump_any();
        }
        Err(ParseError::new("unexpected input", p.end(m)))
    }
}

fn lit(p: &mut Parser<'_>) -> ParseResult<Sp<Lit>> {
    let m = p.start();
    let lit = match p.current().kind {
        UNIT => Lit::Unit,
        LIT(l) => match l {
            LitToken::Bool(b) => Lit::Bool(b),
            LitToken::Int32(i) => Lit::Int32(i),
            LitToken::Str(s, true) => Lit::Str(s),
            LitToken::Str(_, false) => {
                return Err(ParseError::new(
                    "string literal is not terminated by '\"'",
                    p.end(m),
                ));
            }
        },
        _ => return Err(ParseError::new("expected a literal", p.current().span)),
    };
    let span = p.end(m);
    p.bump_any();
    Ok(Sp::new(lit, span))
}

fn ident(p: &mut Parser<'_>, is_upper: bool) -> ParseResult<Ident> {
    match p.current().kind {
        IDENT(id, upper) if upper == is_upper => {
            p.bump_any();
            Ok(id)
        }
        _ => Err(ParseError::new(
            format!(
                "expected {}case identifier",
                if is_upper { "an upper" } else { "a lower" }
            ),
            p.current().span,
        )),
    }
}

#[inline]
fn ident_lower(p: &mut Parser<'_>) -> ParseResult<Ident> {
    ident(p, false)
}

#[inline]
fn ident_upper(p: &mut Parser<'_>) -> ParseResult<Ident> {
    ident(p, true)
}

#[derive(PartialEq)]
enum IdentKind {
    Var,
    Cons,
    Infix,
}

fn ident_or_infix(p: &mut Parser<'_>) -> ParseResult<(Ident, IdentKind)> {
    Ok(match p.current().kind {
        IDENT(id, true) => {
            p.bump_any();
            (id, IdentKind::Cons)
        }
        IDENT(id, false) => {
            p.bump_any();
            (id, IdentKind::Var)
        }
        L_PAREN => {
            p.bump(L_PAREN);
            match p.current().kind {
                INFIX(ident, _) => {
                    p.bump_any();
                    p.expect(R_PAREN)?;
                    (ident, IdentKind::Infix)
                }
                _ => return Err(ParseError::new("expected infix operator", p.current().span)),
            }
        }
        _ => {
            return Err(ParseError::new(
                "expected either an identifier or a parenthesized infix operator",
                p.current().span,
            ));
        }
    })
}

#[derive(PartialEq)]
enum PathKind {
    Path(IdentKind),
    Ident(IdentKind),
}

fn path<'ast>(p: &mut Parser<'ast>) -> ParseResult<(Path<'ast>, PathKind)> {
    let m = p.start();
    let (root, mut kind) = ident_or_infix(p)?;

    {
        let mdot = p.start();
        if kind == IdentKind::Infix && p.eat(DOT) {
            return Err(ParseError::new(
                "unexpected `.` after infix operator",
                p.end(mdot),
            ));
        }
    }

    if !p.at(DOT) {
        return Ok((
            Path::new(root, &[], root.span, p.next_ast_id()),
            PathKind::Ident(kind),
        ));
    }

    let mut access = Vec::new();
    while p.eat(DOT) {
        match p.current().kind {
            IDENT(..) | L_PAREN => {
                let (segment, segment_kind) = ident_or_infix(p)?;
                access.push(segment);
                kind = segment_kind;
                match kind {
                    IdentKind::Var => (),
                    IdentKind::Cons | IdentKind::Infix => break,
                }
            }
            EOF => return Err(ParseError::new("incomplete path", p.end(m))),
            _ => return Err(ParseError::new("unexpected token in path", p.end(m))),
        }
    }

    Ok((
        Path::new(root, alloc_iter!(p, access), p.end(m), p.next_ast_id()),
        PathKind::Path(kind),
    ))
}

fn path_without_infix<'ast>(p: &mut Parser<'ast>) -> ParseResult<Path<'ast>> {
    let m = p.start();
    let root = ident_lower(p)?;
    let mut access = Vec::new();
    while !p.at(EOF) && p.eat(DOT) {
        access.push(ident_lower(p)?);
    }
    Ok(Path::new(
        root,
        alloc_iter!(p, access),
        p.end(m),
        p.next_ast_id(),
    ))
}

fn expr_path<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    let m = p.start();
    let (path, kind) = path(p)?;
    Ok(Expr::new(
        match kind {
            PathKind::Path(IdentKind::Cons) | PathKind::Ident(IdentKind::Cons) => {
                ExprKind::Cons(path)
            }
            _ => ExprKind::Path(path),
        },
        p.end(m),
        p.next_ast_id(),
    ))
}

#[inline]
fn at_type_atom(p: &Parser<'_>) -> bool {
    matches!(
        p.current().kind,
        IDENT(_, false) | L_PAREN | L_BRACE | L_BRAC | UNIT | VAR(_)
    )
}

fn expr_paren<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    let m = p.start();
    p.bump(L_PAREN);
    let first = expr(p)?;
    if p.eat(R_PAREN) {
        return Ok(first);
    }
    if p.eat(COLON) {
        let t = type_(p)?;
        p.expect(R_PAREN)?;
        return Ok(Expr::new(
            ExprKind::Ann(alloc!(p, first), alloc!(p, t)),
            p.end(m),
            p.next_ast_id(),
        ));
    }
    let mut elements = vec![first];
    while !p.at(EOF) && p.eat(COMMA) {
        elements.push(expr(p)?);
    }
    p.expect(R_PAREN)?;
    Ok(Expr::new(
        ExprKind::Tuple(alloc_iter!(p, elements)),
        p.end(m),
        p.next_ast_id(),
    ))
}

fn expr_lit<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    let l = lit(p)?;
    Ok(Expr::new(ExprKind::Lit(*l), l.span(), p.next_ast_id()))
}

fn expr_atom<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    match p.current().kind {
        IDENT(..) => expr_path(p),
        UNIT | LIT(..) => expr_lit(p),
        L_PAREN => expr_paren(p),
        L_BRACE => expr_record(p),
        L_BRAC => expr_vector(p),
        _ => Err(ParseError::new(
            "expected an atomic expression",
            p.current().span,
        )),
    }
}

fn expr_record<'ast>(_p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    todo!("record literals")
}

fn expr_vector<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    let m = p.start();
    p.bump(L_BRAC);
    let mut elements = Vec::new();
    if !p.at(R_BRAC) {
        elements.push(expr(p)?);
        while !p.at(EOF) && p.eat(COMMA) {
            elements.push(expr(p)?);
        }
    }
    p.expect(R_BRAC)?;
    Ok(Expr::new(
        ExprKind::Vector(alloc_iter!(p, elements)),
        p.end(m),
        p.next_ast_id(),
    ))
}

fn expr_if<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    let m = p.start();
    p.bump(KW_IF);
    let cond = expr(p)?;
    p.expect(KW_THEN)?;
    let then = expr(p)?;
    p.expect(KW_ELSE)?;
    let els = expr(p)?;
    Ok(Expr::new(
        ExprKind::If(alloc!(p, cond), alloc!(p, then), alloc!(p, els)),
        p.end(m),
        p.next_ast_id(),
    ))
}

fn expr_let<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    let m = p.start();
    p.bump(KW_LET);
    let mut bindings = Vec::new();
    while !p.at(EOF) && !p.at(KW_IN) {
        let pat = pattern(p)?;
        p.expect(EQUAL)?;
        let expr = expr(p)?;
        bindings.push((pat, expr));
        if !p.eat(COMMA) {
            break;
        }
    }
    p.expect(KW_IN)?;
    if bindings.is_empty() {
        return Err(ParseError::new("let expression missing binds", p.end(m)));
    }
    let body = expr(p)?;
    Ok(Expr::new(
        ExprKind::Let(alloc_iter!(p, bindings), alloc!(p, body)),
        p.end(m),
        p.next_ast_id(),
    ))
}

fn expr_case<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    let m = p.start();
    p.bump(KW_CASE);
    let e = expr_atom(p)?;
    p.expect(L_BRACE)?;
    let mut arms = Vec::new();
    while !p.at(EOF) && !p.at(R_BRACE) {
        let pat = pattern(p)?;
        p.expect(EQUAL_ARROW)?;
        let expr = expr(p)?;
        arms.push((pat, expr));
        if !p.eat(COMMA) {
            break;
        }
    }
    p.expect(R_BRACE)?;
    if arms.is_empty() {
        return Err(ParseError::new("case has no arms", p.end(m)));
    }
    Ok(Expr::new(
        ExprKind::Case(alloc!(p, e), alloc_iter!(p, arms)),
        p.end(m),
        p.next_ast_id(),
    ))
}

fn expr_lambda<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    let m = p.start();
    p.bump(BACKSLASH);
    let mut args = Vec::new();
    while !p.at(EOF) && !p.at(ARROW) {
        args.push(pat_atom(p)?);
    }
    p.expect(ARROW)?;
    if args.is_empty() {
        return Err(ParseError::new(
            "lambda requires at least one argument",
            p.end(m),
        ));
    }
    let body = expr(p)?;
    Ok(Expr::new(
        ExprKind::Lambda(Lambda {
            args: alloc_iter!(p, args),
            body: alloc!(p, body),
        }),
        p.end(m),
        p.next_ast_id(),
    ))
}

fn expr_<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    match p.current().kind {
        KW_IF => expr_if(p),
        KW_LET => expr_let(p),
        KW_CASE => expr_case(p),
        BACKSLASH => expr_lambda(p),
        _ => expr_bp(p, 0),
    }
}

fn at_expr_atom(p: &Parser<'_>) -> bool {
    matches!(
        p.current().kind,
        IDENT(..) | UNIT | LIT(..) | L_PAREN | L_BRAC
    )
}

fn expr_app<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    let m = p.start();
    let head = expr_atom(p)?;
    let mut args = Vec::new();
    while !p.at(EOF) && (at_expr_atom(p) || p.at(AT)) {
        args.push(expr_atom(p)?);
    }
    if args.is_empty() {
        Ok(head)
    } else {
        Ok(Expr::new(
            ExprKind::Call(alloc!(p, head), alloc_iter!(p, args)),
            p.end(m),
            p.next_ast_id(),
        ))
    }
}

fn expr_bp<'ast>(p: &mut Parser<'ast>, min_bp: u8) -> ParseResult<Expr<'ast>> {
    let m = p.start();
    let mut lhs = expr_app(p)?;
    while let Some(((l_bp, r_bp), op)) = infix_op(p)
        && l_bp >= min_bp
    {
        p.bump_any();
        let rhs = expr_bp(p, r_bp)?;
        lhs = Expr::new(
            ExprKind::Call(alloc!(p, op), alloc_iter!(p, [lhs, rhs])),
            p.end(m),
            p.next_ast_id(),
        );
    }
    Ok(lhs)
}

fn infix_op<'ast>(p: &mut Parser<'ast>) -> Option<((u8, u8), Expr<'ast>)> {
    let (id, c) = match p.current().kind {
        INFIX(id, c) => (id, c),
        _ => return None,
    };
    let bp: (u8, u8) = match c {
        '=' | '<' | '>' | '|' | '&' => (1, 2),
        '^' => (3, 4),
        '+' | '-' => (5, 6),
        '*' | '/' => (7, 8),
        ':' => (2, 1),
        _ => unreachable!(),
    };
    let op = Expr::new(
        ExprKind::Path(Path::new(id, &[], p.current().span, p.next_ast_id())),
        p.current().span,
        p.next_ast_id(),
    );
    Some((bp, op))
}

pub fn expr<'ast>(p: &mut Parser<'ast>) -> ParseResult<Expr<'ast>> {
    let m = p.start();
    let first = expr_(p)?;
    if p.eat(SEMICOLON) {
        let second = expr(p)?;
        Ok(Expr::new(
            ExprKind::Seq(alloc!(p, first), alloc!(p, second)),
            p.end(m),
            p.next_ast_id(),
        ))
    } else {
        Ok(first)
    }
}

fn pat_lit<'ast>(p: &mut Parser<'ast>) -> ParseResult<Pat<'ast>> {
    let l = lit(p)?;
    Ok(Pat::new(PatKind::Lit(*l), l.span(), p.next_ast_id()))
}

fn pat_atom<'ast>(p: &mut Parser<'ast>) -> ParseResult<Pat<'ast>> {
    let m = p.start();
    match p.current().kind {
        UNDERSCORE => {
            p.bump(UNDERSCORE);
            Ok(Pat::new(PatKind::Wild, p.end(m), p.next_ast_id()))
        }
        IDENT(id, false) => {
            p.bump_any();
            Ok(Pat::new(
                PatKind::Var(Id::new(id, p.next_ast_id())),
                p.end(m),
                p.next_ast_id(),
            ))
        }
        IDENT(id, true) => {
            p.bump_any();
            Ok(Pat::new(
                PatKind::Cons(Path::new(id, &[], id.span, p.next_ast_id()), &[]),
                p.end(m),
                p.next_ast_id(),
            ))
        }
        UNIT | LIT(..) => pat_lit(p),
        L_PAREN => pat_paren(p),
        _ => Err(ParseError::new("expected an atomic pattern", p.end(m))),
    }
}

fn pat_paren<'ast>(p: &mut Parser<'ast>) -> ParseResult<Pat<'ast>> {
    let m = p.start();
    p.bump(L_PAREN);
    let first = pattern(p)?;
    if p.eat(R_PAREN) {
        return Ok(first);
    }
    if p.eat(COLON) {
        let t = type_(p)?;
        p.expect(R_PAREN)?;
        return Ok(Pat::new(
            PatKind::Ann(alloc!(p, first), alloc!(p, t)),
            p.end(m),
            p.next_ast_id(),
        ));
    }
    let mut rest = vec![first];
    while !p.at(EOF) && p.eat(COMMA) {
        rest.push(pattern(p)?);
    }
    p.expect(R_PAREN)?;
    Ok(Pat::new(
        PatKind::Tuple(alloc_iter!(p, rest)),
        p.end(m),
        p.next_ast_id(),
    ))
}

fn pat_ctor<'ast>(p: &mut Parser<'ast>) -> ParseResult<Pat<'ast>> {
    fn at_pat_atom(p: &Parser<'_>) -> bool {
        matches!(
            p.current().kind,
            UNDERSCORE | IDENT { .. } | UNIT | LIT(..) | L_PAREN
        )
    }
    match p.current().kind {
        IDENT(..) => {
            let m = p.start();
            let (path, kind) = path(p)?;
            match kind {
                PathKind::Ident(IdentKind::Infix)
                | PathKind::Path(IdentKind::Var | IdentKind::Infix) => {
                    return Err(ParseError::new(
                        "pattern paths must be either fresh variable bindings or paths to constructors",
                        path.span(),
                    ));
                }
                PathKind::Ident(IdentKind::Var) => {
                    return Ok(Pat::new(
                        PatKind::Var(Id::new(path.leaf(), p.next_ast_id())),
                        path.span(),
                        p.next_ast_id(),
                    ));
                }
                _ => (),
            }
            let args = if at_pat_atom(p) {
                let mut args = Vec::new();
                args.push(pat_atom(p)?);
                while at_pat_atom(p) {
                    args.push(pat_atom(p)?);
                }
                args
            } else {
                Vec::new()
            };
            Ok(Pat::new(
                PatKind::Cons(path, alloc_iter!(p, args)),
                p.end(m),
                p.next_ast_id(),
            ))
        }
        _ => pat_atom(p),
    }
}

fn pattern<'ast>(p: &mut Parser<'ast>) -> ParseResult<Pat<'ast>> {
    let m = p.start();
    let first = pat_ctor(p)?;
    let mut rest = Vec::new();
    while !p.at(EOF) && p.eat(PIPE) {
        rest.push(pat_ctor(p)?);
    }
    if rest.is_empty() {
        Ok(first)
    } else {
        rest.splice(0..0, [first]);
        Ok(Pat::new(
            PatKind::Or(alloc_iter!(p, rest)),
            p.end(m),
            p.next_ast_id(),
        ))
    }
}

fn type_path<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Type<'ast>>> {
    let path = path_without_infix(p)?;
    if path.access.is_empty()
        && let Some(base) = base_type(path.root)
    {
        return Ok(Sp::new(Type::Base(base), path.span()));
    }
    Ok(Sp::new(Type::App(path, &[]), path.span()))
}

fn type_atom<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Type<'ast>>> {
    let m = p.start();
    match p.current().kind {
        UNIT => {
            let span = p.current().span;
            p.bump(UNIT);
            Ok(Sp::new(Type::Base(BaseType::Unit), span))
        }
        IDENT { .. } => type_path(p),
        L_PAREN => type_paren(p),
        L_BRACE => type_row(p),
        L_BRAC => type_vector(p),
        VAR(id) => {
            p.bump_any();
            Ok(Sp::new(Type::Var(Id::new(id, p.next_ast_id())), p.end(m)))
        }
        _ => Err(ParseError::new("expected atomic type", p.end(m))),
    }
}

fn type_vector<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Type<'ast>>> {
    let m = p.start();
    p.bump(L_BRAC);
    let typ = type_(p)?;
    p.expect(R_BRAC)?;
    Ok(Sp::new(Type::Vector(alloc!(p, typ)), p.end(m)))
}

fn base_type(id: Ident) -> Option<BaseType> {
    Some(match id.sym.as_str() {
        "bool" => BaseType::Bool,
        "str" => BaseType::Str,
        "i32" => BaseType::Int32,
        _ => return None,
    })
}

fn type_paren<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Type<'ast>>> {
    let m = p.start();
    p.bump(L_PAREN);
    let first = type_(p)?;
    if p.eat(R_PAREN) {
        return Ok(Sp::new(first.value, p.end(m)));
    }
    let mut elements = vec![first];
    while !p.at(EOF) && p.eat(COMMA) {
        elements.push(type_(p)?);
    }
    p.expect(R_PAREN)?;
    Ok(Sp::new(Type::Tuple(alloc_iter!(p, elements)), p.end(m)))
}

fn type_row<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Type<'ast>>> {
    let m = p.start();
    p.bump(L_BRACE);

    let mut fields = Vec::new();
    while !p.at(EOF) && !p.at(R_BRACE) && !p.at(PIPE) {
        let id = ident_lower(p)?;
        p.expect(COLON)?;
        let typ = type_(p)?;
        fields.push((Id::new(id, p.next_ast_id()), typ));
        if !p.eat(COMMA) {
            break;
        }
    }

    let ext = if p.eat(PIPE) {
        if fields.is_empty() {
            return Err(ParseError::new(
                "cannot extend a record by nothing",
                p.end(m),
            ));
        }
        Some(alloc!(p, type_atom(p)?))
    } else {
        None
    };

    p.expect(R_BRACE)?;
    Ok(Sp::new(Type::Row(alloc_iter!(p, fields), ext), p.end(m)))
}

fn type_<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Type<'ast>>> {
    let m = p.start();
    let from = type_app(p)?;
    if p.eat(ARROW) {
        let to = type_(p)?;
        Ok(Sp::new(
            Type::Arrow(alloc!(p, from), alloc!(p, to)),
            p.end(m),
        ))
    } else {
        Ok(from)
    }
}

fn type_app<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Type<'ast>>> {
    let m = p.start();
    let head = type_atom(p)?;
    let mut args = Vec::new();
    while !p.at(EOF) {
        match p.current().kind {
            L_PAREN | UNIT | EXCLAM | VAR(..) | IDENT { .. } => args.push(type_atom(p)?),
            _ => break,
        }
    }
    if args.is_empty() {
        Ok(head)
    } else {
        match *head {
            Type::App(cons_path, []) => Ok(Sp::new(
                Type::App(cons_path, alloc_iter!(p, args)),
                p.end(m),
            )),
            _ => Err(ParseError::new("expected a type path", head.span())),
        }
    }
}

fn type_decl<'ast>(p: &mut Parser<'ast>) -> ParseResult<TypeDecl<'ast>> {
    let m = p.start();
    p.bump(KW_TYPE);
    let id = Id::new(ident_lower(p)?, p.next_ast_id());
    let mut vars = Vec::new();
    while !p.at(EOF)
        && let VAR(s) = p.current().kind
    {
        p.bump_any();
        vars.push(Id::new(s, p.next_ast_id()));
    }
    let vars = alloc_iter!(p, vars);
    p.expect(EQUAL)?;
    let kind = match p.current().kind {
        PIPE => {
            p.bump(PIPE);
            let mut variants = Vec::new();
            while !p.at(EOF) && !p.at(PIPE) {
                let ctor = ident_upper(p)?;
                let mut args = Vec::new();
                while at_type_atom(p) {
                    let arg = type_atom(p)?;
                    args.push(arg);
                    if let Type::Row(_, Some(ext)) = *arg {
                        return Err(ParseError::new(
                            "only non-extensible records allowed in datatype constructor args",
                            ext.span(),
                        ));
                    }
                }
                variants.push((Id::new(ctor, p.next_ast_id()), alloc_iter!(p, args)));
                if !p.eat(COMMA) {
                    break;
                }
            }
            p.expect(PIPE)?;
            TypeDeclKind::Variant(alloc_iter!(p, variants))
        }
        _ => {
            let typ = type_(p)?;
            TypeDeclKind::Alias(alloc!(p, typ))
        }
    };
    Ok(TypeDecl {
        id,
        vars,
        kind,
        span: p.end(m),
    })
}

fn struct_item<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Item<'ast>>> {
    match p.current().kind {
        KW_TYPE => struct_item_type_decl(p),
        KW_VAL => struct_item_val(p),
        KW_MOD => struct_item_mod(p),
        KW_EXTERNAL => struct_item_external(p),
        _ => Err(ParseError::new("expected structure item", p.current().span)),
    }
}

fn struct_item_type_decl<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Item<'ast>>> {
    let m = p.start();
    let mut decl_group = vec![type_decl(p)?];
    while !p.at(EOF) && p.eat(KW_AND) {
        decl_group.push(type_decl(p)?);
    }
    Ok(Sp::new(Item::Type(alloc_iter!(p, decl_group)), p.end(m)))
}

fn struct_item_val<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Item<'ast>>> {
    let m = p.start();
    p.bump(KW_VAL);
    let (id, kind) = ident_or_infix(p)?;
    let id = Id::new(id, p.next_ast_id());
    if kind == IdentKind::Cons {
        return Err(ParseError::new(
            "expected lowercase identifier or parenthesized infix operator for value name",
            id.ident.span,
        ));
    }
    let mut args = Vec::new();
    while !(p.at(EOF) || p.at(EQUAL) || p.at(COLON)) {
        args.push(pat_atom(p)?);
    }
    let typ = if p.eat(COLON) {
        Some(alloc!(p, type_(p)?))
    } else {
        None
    };
    p.expect(EQUAL)?;
    let body = alloc!(p, expr(p)?);
    if args.is_empty() {
        Ok(Sp::new(Item::Value(id, typ, body), p.end(m)))
    } else {
        Ok(Sp::new(
            Item::Value(
                id,
                typ,
                alloc!(
                    p,
                    Expr::new(
                        ExprKind::Lambda(Lambda {
                            args: alloc_iter!(p, args),
                            body,
                        }),
                        body.span,
                        p.next_ast_id(),
                    )
                ),
            ),
            p.end(m),
        ))
    }
}

fn struct_item_mod<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Item<'ast>>> {
    let m = p.start();
    p.bump(KW_MOD);
    let id = ident_lower(p)?;
    p.expect(EQUAL)?;
    let me = mod_expr(p)?;
    Ok(Sp::new(
        Item::Mod(Id::new(id, p.next_ast_id()), alloc!(p, me)),
        p.end(m),
    ))
}

fn lit_str(p: &mut Parser<'_>) -> ParseResult<Ident> {
    match p.current().kind {
        LIT(LitToken::Str(sym, true)) => {
            let m = p.start();
            p.bump_any();
            Ok(Ident::new(sym, p.end(m)))
        }
        LIT(LitToken::Str(_, false)) => Err(ParseError::new(
            "string literal is not terminated by '\"'",
            p.current().span,
        )),
        _ => Err(ParseError::new(
            "expected string literal in external declaration",
            p.current().span,
        )),
    }
}

fn struct_item_external<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<Item<'ast>>> {
    let m = p.start();
    p.bump(KW_EXTERNAL);
    let (ident, kind) = ident_or_infix(p)?;
    if kind == IdentKind::Cons {
        return Err(ParseError::new(
            "cannot declare external constructor",
            ident.span,
        ));
    }
    p.expect(COLON)?;
    let t = type_(p)?;
    p.expect(EQUAL)?;
    let s = lit_str(p)?;
    Ok(Sp::new(
        Item::External(Id::new(ident, p.next_ast_id()), alloc!(p, t), s),
        p.end(m),
    ))
}

pub fn mod_expr<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<ModExpr<'ast>>> {
    match p.current().kind {
        IDENT { .. } => mod_expr_path(p),
        L_BRACE => mod_expr_struct(p),
        KW_IMPORT => mod_expr_import(p),
        L_PAREN => {
            p.bump(L_PAREN);
            let me = mod_expr(p)?;
            p.expect(R_PAREN)?;
            Ok(me)
        }
        _ => Err(ParseError::new("expected module", p.current().span)),
    }
}

fn mod_expr_path<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<ModExpr<'ast>>> {
    let m = p.start();
    let path = path_without_infix(p)?;
    Ok(Sp::new(ModExpr::Path(path), p.end(m)))
}

fn mod_expr_struct<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<ModExpr<'ast>>> {
    let m = p.start();
    p.expect(L_BRACE)?;
    let mut items = Vec::new();
    while !p.at(EOF) && !p.at(R_BRACE) {
        items.push(struct_item(p)?);
    }
    let span = p.end(m);
    p.expect(R_BRACE)?;
    Ok(Sp::new(ModExpr::Struct(alloc_iter!(p, items)), span))
}

fn mod_expr_import<'ast>(p: &mut Parser<'ast>) -> ParseResult<Sp<ModExpr<'ast>>> {
    let m = p.start();
    p.expect(KW_IMPORT)?;
    let path = lit_str(p)?;
    let span = path.span;
    let path = std::path::PathBuf::from(path.to_string());
    let source_id = parse_import(&path, span, p)?;
    Ok(Sp::new(ModExpr::Import(source_id), p.end(m)))
}
