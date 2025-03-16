use base::hash::Map;
use span::Ident;
use syntax::ast;

use crate::{lower::LoweringContext, mir::Label};

// The pattern match compilation algorithm is due to Jules Jacobs
// https://julesjacobs.com/notes/patternmatching/patternmatching.pdf
// with help from Yorick Peterse's implementation
// https://github.com/yorickpeterse/pattern-matching-in-rust
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
// pattern matchin will use many-test clauses depending on the arity
// of constructors.
//
// The goal is an algorithm that takes such an input list of clauses
// and outputs a decision tree of _primitive_ cases that test against
// a single constructor:
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
// Compiling Pattern Matching to Good Decision Trees, Luc Maranget
// https://compiler.club/compiling-pattern-matching/
// https://github.com/SomewhatML/match-compile/

#[derive(Clone, Debug)]
pub enum DecisionTree {
    Fail,
    Leaf(usize),
    Switch(Label, Vec<Case>, Option<Box<DecisionTree>>),
}

#[derive(Clone, Debug)]
pub struct Case {
    constructor: Constructor,
    variables: Vec<Ident>,
    tree: DecisionTree,
}

#[derive(Clone, Copy, Debug)]
pub enum Constructor {
    Bool(bool),
    Tuple(usize),
    Ident(Ident),
}

#[derive(Default)]
struct Matrix<'ast> {
    clauses: Vec<Clause<'ast>>,
}

// A list of tests and the corresponding action.
struct Clause<'ast> {
    tests: Vec<Test<'ast>>,
    body: Body,
}

// Test a variable against a pattern (id is pat).
struct Test<'ast> {
    id: Ident,
    pat: &'ast ast::Pat<'ast>,
}

impl<'ast> Test<'ast> {
    fn new(id: Ident, pat: &'ast ast::Pat<'ast>) -> Self {
        Test { id, pat }
    }
}

struct Body {
    bindings: Vec<(Ident, Ident)>,
    action: usize,
}

impl Body {
    fn new(action: usize) -> Self {
        Body {
            bindings: Vec::new(),
            action,
        }
    }
}

impl<'ast> Matrix<'ast> {
    fn new_from_case(scrutinee_id: Ident, arms: &'ast [(ast::Pat<'ast>, ast::Expr<'ast>)]) -> Self {
        Self {
            clauses: arms
                .iter()
                .enumerate()
                .map(|(action, (pat, _))| Clause {
                    tests: vec![Test::new(scrutinee_id, pat)],
                    body: Body::new(action),
                })
                .collect(),
        }
    }

    fn branch_variable(&self) -> Option<Ident> {
        let mut counts = Map::default();
        for clause in &self.clauses {
            for test in &clause.tests {
                *counts.entry(&test.id).or_insert(0) += 1;
            }
        }
        self.clauses
            .first()?
            .tests
            .iter()
            .map(|test| test.id)
            .max_by_key(|id| counts[id])
    }

    fn bind_variable_patterns(&mut self) {
        for row in self.clauses.iter_mut() {
            row.tests.retain(|e| {
                if let ast::PatKind::Var(id) = e.pat.kind {
                    row.body.bindings.push((id.ident, e.id));
                    false
                } else {
                    true
                }
            });
        }
    }
}

impl<'ast> LoweringContext<'ast, '_> {
    pub fn match_compile(
        &mut self,
        scrutinee: &'ast ast::Expr<'ast>,
        arms: &'ast [(ast::Pat<'ast>, ast::Expr<'ast>)],
    ) -> (Label, DecisionTree) {
        (Label::ZERO, DecisionTree::Fail)

        // let (label, scrutinee_id, arms) = self.preprocess_case(scrutinee, arms);
        // let mut matrix = Matrix::new_from_case(scrutinee_id, arms);
        // let tree = self.compile(&mut matrix);
        // (label, tree)
    }

    fn compile(&mut self, matrix: &mut Matrix<'ast>) -> DecisionTree {
        // If the matrix has no rows, then we vacuously fail.
        if matrix.clauses.is_empty() {
            return DecisionTree::Fail;
        }

        matrix.bind_variable_patterns();

        // If the first clause has no tests, then we have a successful match.
        if matrix.clauses[0].tests.is_empty() {
            let row = matrix.clauses.remove(0);
            return DecisionTree::Leaf(row.body.action);
        }

        let branch_var = matrix
            .branch_variable()
            .expect("could not get branching var");

        let label = todo!();

        let branch_var_typ = self.get_label_type(label);
        /*self
        .infer_data
        .hir_id_to_type
        .get(&self.get_local_hir_id(branch_var))
        .unwrap_or_else(|| panic!("no type for {branch_var}"));
        */

        let mut cases = Vec::new();

        DecisionTree::Switch(label, cases, None)
    }

    fn specialize(&self, id: Ident, matrix: &Matrix<'ast>) -> Matrix<'ast> {
        let mut matrix = Matrix::default();

        for row in &matrix.clauses {}

        matrix
    }
}
