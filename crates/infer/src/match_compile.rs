use base::{
    hash::{Map, Set},
    pp::{DocArena, DocBuilder, INDENT, IntoDoc},
};
use span::{
    Ident, Span, Sym,
    diag::{Diagnostic, Label, Level},
};

use crate::{
    Res, Var,
    hir::*,
    ty::{BaseType, Ty, TyCtxt, TyKind},
};

// The pattern match compilation algorithm is due to Jules Jacobs
// <https://julesjacobs.com/notes/patternmatching/patternmatching.pdf>
// with help from Yorick Peterse's implementation
// <https://github.com/yorickpeterse/pattern-matching-in-rust>
//
// The algorithm
// -------------
// The following is a rough distillation of Jacobs' notes.
//
// The first step is to recast the expression form
//
//   case a {
//      p1 => e1,
//      p2 => e2,
//      ...
//      pn => en,
//   }
//
// which does implicit tests against a into the internal form
//
//   case {
//      a is p1 => e1,
//      a is p2 => e2,
//      ...
//      a in pn => en,
//   }
//
// where we perform explicit tests (a is pattern). A list of
// such tests is called a _clause_: (a1 is p1), ..., (ak is pk).
// All tests are against variables, since we can hoist complicated
// expressions beforehand.
//
// A case expression gives us a list of 1-test clauses (since the user
// can only write cases against a single scrutinee). The internal
// pattern matching will use many-test clauses depending on the arity
// of constructors.
//
// The goal is an algorithm that takes such an input list of clauses
// and outputs a decision tree of _primitive_ cases that test against
// bare constructors:
//
//   case# a {
//      C a1 ... ak => [A],
//      _           => [B],
//   }
//
// Steps
// -----
// Given a list of clauses, perform the following.
//
//   1. Push tests against bare variables (a is x) into the RHS of
//      case arms using let x = a in RHS, so that all remaining tests
//      are against constructors.
//   2. Select one test (a is C p1 ... pk) in the first clause using a
//      heuristic which will minimize code duplication. A simple heuristic
//      is to choose a test that is present in the most amount of other
//      clauses.
//   3. Generate the primitive case
//         case# a {
//            C a1 ... ak => [A],
//            _           => [B],
//         }
//   4. Create subproblems [A] and [B] by iterating over each clause.
//      If the clause contains
//      (a) a test (a is C p1' ... pk'), then expand to the clause
//          (a1 is p1'), ..., (ak is pk') and add to [A], ensuring the
//          names a1, ..., ak are used consistently.
//      (b) a test (a is D p1' ... pk') and D != C, then add to [B]
//          unchanged.
//      (c) no test for a, then add to both [A] and [B]. Note that each
//          clause can have only one test for a.
//   5. Recursively generate code for [A] and [B] using steps 1-4.
//      The base cases are:
//      (a) Empty clause list: all patterns failed, so we have an
//          nonexhaustive case.
//      (b) Empty first clause / zero tests: the first clause successfully
//          matched, so just return the corresponding case arm action / RHS.
//
// Other references
// ----------------
//   - Compiling Pattern Matching to Good Decision Trees, Luc Maranget
//   - https://compiler.club/compiling-pattern-matching/
//   - https://github.com/SomewhatML/match-compile/

pub fn compile<'a, 't>(
    ctxt: &'t TyCtxt<'t>,
    program: &'a mut Program<'t>,
) -> Result<(), Diagnostic> {
    let mut compiler = MatchCompiler::new(ctxt);
    compiler.visit_program(program);

    if !compiler.errors.is_empty() {
        // TODO. Support multiple diagnostics in driver.
        let error = compiler.errors.pop().unwrap();

        return Err(error.into());
    }

    Ok(())
}

#[derive(Clone, Debug)]
pub enum DecisionTree<'t> {
    Fail,
    Leaf(Body<'t>),
    Switch(Var<'t>, Vec<Case<'t>>, Option<Box<DecisionTree<'t>>>),
}

#[derive(Clone, Debug)]
pub struct Case<'t> {
    pub constructor: Constructor,
    pub variables: Vec<Var<'t>>,
    pub tree: DecisionTree<'t>,
}

impl<'t> Case<'t> {
    pub fn new(constructor: Constructor, variables: Vec<Var<'t>>, tree: DecisionTree<'t>) -> Self {
        Self {
            constructor,
            variables,
            tree,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Constructor {
    Unit,
    Bool(bool),
    Tuple(usize),
    Ident(Ident, usize),
}

#[derive(Clone, Debug)]
pub struct Body<'t> {
    pub bindings: Vec<(Var<'t>, Var<'t>)>,
    pub action: usize,
}

impl<'t> Body<'t> {
    fn new(action: usize) -> Self {
        Body {
            bindings: Vec::new(),
            action,
        }
    }
}

const BOOL_TRUE_IDX: usize = 0;
const BOOL_FALSE_IDX: usize = 1;

#[derive(Default, Debug)]
struct Matrix<'a, 't> {
    clauses: Vec<Clause<'a, 't>>,
}

// A list of tests and the corresponding action.
#[derive(Clone, Debug)]
struct Clause<'a, 't> {
    tests: Vec<Test<'a, 't>>,
    body: Body<'t>,
}

impl<'a, 't> Clause<'a, 't> {
    fn new(tests: Vec<Test<'a, 't>>, body: Body<'t>) -> Self {
        Self { tests, body }
    }

    fn remove_test(&mut self, var: Var<'t>) -> Option<Test<'a, 't>> {
        self.tests
            .iter()
            .position(|t| t.var == var)
            .map(|idx| self.tests.remove(idx))
    }
}

// Test a variable against a pattern (id is pat).
#[derive(Clone, Debug)]
struct Test<'a, 't> {
    var: Var<'t>,
    pat: &'a Pat<'t>,
}

impl<'a, 't> Test<'a, 't> {
    fn new(var: Var<'t>, pat: &'a Pat<'t>) -> Self {
        Test { var, pat }
    }
}

impl<'a, 't> Matrix<'a, 't> {
    fn new(clauses: Vec<Clause<'a, 't>>) -> Self {
        Self { clauses }
    }

    fn new_from_case(scrutinee: Var<'t>, arms: &'a [(Pat<'t>, Expr<'t>)]) -> Self {
        Self::new(
            arms.iter()
                .enumerate()
                .map(|(idx, (pat, _))| Clause {
                    tests: vec![Test::new(scrutinee, pat)],
                    body: Body::new(idx),
                })
                .collect(),
        )
    }

    fn branch_variable(&self) -> Option<Var<'t>> {
        let mut counts = Map::default();
        for clause in &self.clauses {
            for test in &clause.tests {
                *counts.entry(&test.var).or_insert(0) += 1;
            }
        }
        self.clauses
            .first()?
            .tests
            .iter()
            .map(|test| test.var)
            .max_by_key(|var| counts[var])
    }
}

enum MatchError {
    RedundantArms(Span, Vec<Span>),
}

impl From<MatchError> for Diagnostic {
    fn from(value: MatchError) -> Self {
        match value {
            MatchError::RedundantArms(main_span, arm_spans) => {
                let mut labels = vec![Label::new(main_span, "").primary()];
                labels.extend(arm_spans.iter().map(|span| Label::new(*span, "")));
                Diagnostic::new(Level::Warn)
                    .with_message("case has redundant arms")
                    .with_labels(labels)
            }
        }
    }
}

struct MatchCompiler<'t> {
    ctxt: &'t TyCtxt<'t>,

    reachable: Set<usize>,

    errors: Vec<MatchError>,
}

impl<'t> HirVisitor<'t> for MatchCompiler<'t> {
    fn visit_expr(&mut self, expr: &mut Expr<'t>) {
        match &mut expr.kind {
            ExprKind::Case(scrutinee, arms, tree) => {
                assert!(tree.is_none());

                self.reachable.clear();

                let mut var = Var::new(
                    Ident::new(Sym::intern("~case"), scrutinee.span),
                    Res::Local(self.ctxt.new_res_id()),
                    scrutinee.span,
                );
                var.typ = scrutinee.typ;
                let mut matrix = Matrix::new_from_case(var, arms);

                let tree_ = self.compile_matrix(&mut matrix);

                //println!("{:#?}", tree);

                let doc_arena = DocArena::default();
                println!("{}", tree_.to_doc(&doc_arena).pretty_string(100));

                tree.replace(tree_);

                if !self.reachable.is_empty() {
                    let mut spans = Vec::new();
                    for action in 0..arms.len() {
                        if !self.reachable.contains(&action) {
                            let (pat, expr) = &arms[action];
                            let arm_span = pat.span.merge(expr.span);
                            spans.push(arm_span);
                        }
                    }
                    if !spans.is_empty() {
                        self.errors
                            .push(MatchError::RedundantArms(scrutinee.span, spans));
                    }
                    self.reachable.clear();
                }
            }
            _ => expr.visit_with(self),
        }
    }
}

impl<'t> MatchCompiler<'t> {
    fn new(ctxt: &'t TyCtxt<'t>) -> Self {
        Self {
            ctxt,
            reachable: Set::default(),
            errors: Vec::new(),
        }
    }

    fn generate_typed_vars(&self, typs: &'t [Ty<'t>]) -> Vec<Var<'t>> {
        let mut vars = Vec::with_capacity(typs.len());
        for (idx, typ) in typs.iter().enumerate() {
            let mut var = Var::new(
                Ident::new(Sym::intern(&format!("~t{idx}")), Span::dummy()),
                Res::Local(self.ctxt.new_res_id()),
                Span::dummy(),
            );
            var.typ = Some(*typ);
            vars.push(var);
        }
        vars
    }

    fn compile_matrix<'a>(&mut self, matrix: &mut Matrix<'a, 't>) -> DecisionTree<'t> {
        // If the matrix has no rows, then we vacuously fail.
        if matrix.clauses.is_empty() {
            return DecisionTree::Fail;
        }

        for row in matrix.clauses.iter_mut() {
            row.tests.retain(|e| match e.pat.kind {
                PatKind::Var(var) => {
                    row.body.bindings.push((var, e.var));
                    false
                }
                PatKind::Wild => {
                    let mut var = Var::new(
                        Ident::new(Sym::intern("~w"), e.pat.span),
                        Res::Local(self.ctxt.new_res_id()),
                        e.pat.span,
                    );
                    var.typ = e.pat.typ;
                    row.body.bindings.push((var, e.var));
                    false
                }
                _ => true,
            });
        }

        // If the first clause has no tests, then we have a successful match.
        if matrix.clauses[0].tests.is_empty() {
            let row = matrix.clauses.remove(0);
            self.reachable.insert(row.body.action);
            return DecisionTree::Leaf(row.body);
        }

        let branch_var = matrix
            .branch_variable()
            .expect("could not get branching var");

        let branch_typ = branch_var
            .typ
            .expect("match compilation requires typed HIR");

        if let Some(res) = branch_typ.as_user() {
            let adt = self.ctxt.get_adt(res).unwrap();
            let num_cons = adt.constructors.len();
            let mut cases = Vec::with_capacity(num_cons);
            for cons in adt.constructors.values() {
                let vars = self.generate_typed_vars(cons.args);
                // OK because adt.constructors is an index map
                cases.push((
                    Constructor::Ident(cons.var.id, cons.index),
                    vars,
                    Vec::new(),
                ));
            }
            return DecisionTree::Switch(
                branch_var,
                self.compile_cases(matrix, branch_var, cases),
                None,
            );
        }

        match branch_typ.kind() {
            TyKind::Base(BaseType::Unit) => {
                let cases = vec![(Constructor::Unit, Vec::new(), Vec::new())];
                DecisionTree::Switch(
                    branch_var,
                    self.compile_cases(matrix, branch_var, cases),
                    None,
                )
            }
            TyKind::Base(BaseType::Bool) => {
                // FIXME. enforce idx
                let cases = vec![
                    // BOOL_TRUE_IDX
                    (Constructor::Bool(true), Vec::new(), Vec::new()),
                    // BOOL_FALSE_IDX
                    (Constructor::Bool(false), Vec::new(), Vec::new()),
                ];
                DecisionTree::Switch(
                    branch_var,
                    self.compile_cases(matrix, branch_var, cases),
                    None,
                )
            }
            TyKind::Base(_) => todo!("add support for branching on primitives"),
            TyKind::Tuple(typs) => {
                let vars = self.generate_typed_vars(typs);
                let cases = vec![(Constructor::Tuple(typs.len()), vars, Vec::new())];
                DecisionTree::Switch(
                    branch_var,
                    self.compile_cases(matrix, branch_var, cases),
                    None,
                )
            }
            TyKind::Vector(_) => todo!("add support for matching vectors"),
            TyKind::User(..)
            | TyKind::App(..)
            | TyKind::Arrow(..)
            | TyKind::Var(_)
            | TyKind::Skolem(_)
            | TyKind::Uni(_) => {
                println!("{matrix:#?}");
                unreachable!("tried to match on {branch_typ}")
            }
        }
    }

    fn compile_cases<'a>(
        &mut self,
        matrix: &mut Matrix<'a, 't>,
        branch_var: Var<'t>,
        mut cases: Vec<(Constructor, Vec<Var<'t>>, Vec<Clause<'a, 't>>)>,
    ) -> Vec<Case<'t>> {
        for clause in &mut matrix.clauses {
            if let Some(test) = clause.remove_test(branch_var) {
                let tests = &mut clause.tests;
                match &test.pat.kind {
                    PatKind::Lit(Lit::Unit) => {
                        cases[0]
                            .2
                            .push(Clause::new(tests.to_vec(), clause.body.clone()));
                    }
                    PatKind::Lit(Lit::Bool(b)) => {
                        let idx = if *b { BOOL_TRUE_IDX } else { BOOL_FALSE_IDX };
                        cases[idx]
                            .2
                            .push(Clause::new(tests.to_vec(), clause.body.clone()));
                    }
                    PatKind::Tuple(pats) => {
                        if let Constructor::Tuple(n) = cases[0].0
                            && n == pats.len()
                        {
                            for (var, pat) in cases[0].1.iter().zip(pats) {
                                tests.push(Test::new(*var, pat));
                            }
                            cases[0]
                                .2
                                .push(Clause::new(tests.to_vec(), clause.body.clone()));
                        }
                    }
                    PatKind::Cons(cons_var, args) => {
                        let cons = self
                            .ctxt
                            .get_constructor(cons_var.res)
                            .unwrap_or_else(|| panic!("could not find constructor for {cons_var}"));
                        let idx = cons.index;
                        for (var, pat) in cases[idx].1.iter().zip(args) {
                            tests.push(Test::new(*var, pat));
                        }
                        // FIXME(perf)
                        cases[idx]
                            .2
                            .push(Clause::new(tests.to_vec(), clause.body.clone()));
                    }
                    PatKind::Ann(_pat, _) => todo!(),
                    _ => (),
                }
            } else {
                for (_, _, clauses) in &mut cases {
                    clauses.push(clause.clone());
                }
            }
        }

        cases
            .into_iter()
            .map(|(cons, vars, clauses)| {
                let mut matrix = Matrix::new(clauses);
                Case::new(cons, vars, self.compile_matrix(&mut matrix))
            })
            .collect()
    }
}

impl<'t> DecisionTree<'t> {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match self {
            DecisionTree::Fail => arena.text("fail"),
            DecisionTree::Leaf(body) => arena
                .intersperse(
                    body.bindings
                        .iter()
                        .map(|(x, y)| x.into_doc(arena).append(" := ").append(y.into_doc(arena))),
                    arena.line(),
                )
                .append(if body.bindings.is_empty() {
                    arena.empty()
                } else {
                    arena.line()
                })
                .append(arena.text("action "))
                .append(arena.text(body.action.to_string())),
            DecisionTree::Switch(var, cases, _tree) => {
                arena.text("switch ").append(var.into_doc(arena)).append(
                    arena
                        .line()
                        .append(
                            arena.intersperse(
                                cases.iter().map(|case| case.to_doc(arena)),
                                arena.line(),
                            ),
                        )
                        .nest(INDENT),
                )
            }
        }
    }
}

impl Constructor {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        match self {
            Constructor::Unit => arena.text("()"),
            Constructor::Bool(b) => arena.text(b.to_string()),
            Constructor::Tuple(n) => arena.text(format!("({n})")),
            Constructor::Ident(id, _) => arena.text(id.to_string()),
        }
    }
}

impl<'t> Case<'t> {
    pub fn to_doc<'a>(&self, arena: &'a DocArena<'a>) -> DocBuilder<'a> {
        self.constructor
            .to_doc(arena)
            .append(if self.variables.is_empty() {
                arena.empty()
            } else {
                arena
                    .intersperse(
                        self.variables.iter().map(|var| var.into_doc(arena)),
                        arena.text(", "),
                    )
                    .enclose("(", ")")
            })
            .append(" => ")
            .append(arena.line().append(self.tree.to_doc(arena)).nest(INDENT))
    }
}
