use base::hash::Map;
use hir::{CaseArm, Expr, Pat, PatKind};
use span::Ident;

use crate::{lower::LoweringContext, mir::Label};

// References
// ----------
// Compiling Pattern Matching to Good Decision Trees, Luc Maranget
// https://compiler.club/compiling-pattern-matching/
// https://julesjacobs.com/notes/patternmatching/patternmatching.pdf
// https://github.com/yorickpeterse/pattern-matching-in-rust
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
struct Matrix<'hir> {
    rows: Vec<Row<'hir>>,
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

struct Row<'hir> {
    entries: Vec<Entry<'hir>>,
    body: Body,
}

struct Entry<'hir> {
    id: Ident,
    pat: &'hir Pat<'hir>,
}

impl<'hir> Entry<'hir> {
    fn new(id: Ident, pat: &'hir Pat<'hir>) -> Self {
        Entry { id, pat }
    }
}

impl<'hir> Matrix<'hir> {
    fn new_from_case(scrutinee_id: Ident, arms: &'hir [CaseArm<'hir>]) -> Self {
        let rows: Vec<_> = arms
            .iter()
            .enumerate()
            .map(|(action, (pat, _))| Row {
                entries: vec![Entry::new(scrutinee_id, pat)],
                body: Body::new(action),
            })
            .collect();
        Matrix { rows }
    }

    fn branch_var(&self) -> Option<Ident> {
        let mut counts = Map::default();
        for row in &self.rows {
            for entry in &row.entries {
                *counts.entry(&entry.id).or_insert(0) += 1;
            }
        }
        self.rows
            .get(0)?
            .entries
            .iter()
            .map(|e| e.id)
            .max_by_key(|id| counts[id])
    }

    fn bind_variable_patterns(&mut self) {
        for row in self.rows.iter_mut() {
            row.entries.retain(|e| {
                if let PatKind::Var(id, _) = e.pat.kind {
                    row.body.bindings.push((id, e.id));
                    false
                } else {
                    true
                }
            });
        }
    }
}

struct Compiler<'a, 'hir> {
    ctx: &'a LoweringContext<'hir>,
}

impl<'a, 'hir> Compiler<'a, 'hir> {
    fn compile(&mut self, matrix: &mut Matrix<'hir>) -> DecisionTree {
        // If the matrix has no rows, then we vacuously fail.
        if matrix.rows.is_empty() {
            return DecisionTree::Fail;
        }

        matrix.bind_variable_patterns();

        if matrix.rows[0].entries.is_empty() {
            let row = matrix.rows.remove(0);
            return DecisionTree::Leaf(row.body.action);
        }

        let branch_var = matrix.branch_var().expect("Could not get branching var");

        let label = todo!(); // self.ctx.get_id_label(branch_var);

        let mut cases = Vec::new();

        DecisionTree::Switch(label, cases, None)
    }

    fn specialize(&self, id: Ident, matrix: &Matrix<'hir>) -> Matrix<'hir> {
        let (arity, typ) = self
            .ctx
            .infer_data
            .ctor_to_adt
            .get(&id)
            .expect("Variant constructor not found");

        let mut matrix = Matrix::default();

        for row in &matrix.rows {}

        matrix
    }
}

impl<'hir> LoweringContext<'hir> {
    pub fn match_compile(
        &mut self,
        scrutinee: Expr<'hir>,
        arms: &'hir [CaseArm<'hir>],
    ) -> (Label, DecisionTree) {
        let (label, scrutinee_id, arms) = self.preprocess_case(scrutinee, arms);
        let mut matrix = Matrix::new_from_case(scrutinee_id, arms);
        let mut compiler = Compiler { ctx: self };
        let tree = compiler.compile(&mut matrix);
        (label, tree)
    }
}
