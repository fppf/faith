mod closure_convert;
mod lower;
mod pretty;
mod shrink;

pub mod mir;

use base::pp::{DocArena, PRETTY_WIDTH};

// Idea for MIR
// ------------
// After typechecking of HIR, we want a smaller (still-typed) language
// that we can use for latter passes.
//
// Want:
//   - Unpack all patterns into simple bindings (i.e., let (x, y) = (1, 2), z = 3 in e roughly becomes let x = 1 in let y = 2 in let z = 3 in e)
//   - Linearize expresssions, convert to ANF form
//   - Desugar surface language constructs, such as sequence (;) to let statement and if to case
//   - Pattern matches should be compiled to decision trees (nested simple cases)

pub fn lower_and_transform<'t>(
    ctxt: &'t infer::ty::TyCtxt<'t>,
    hir: &infer::hir::Program<'t>,
) -> mir::Program {
    let mut mir = lower::lower(ctxt, hir);

    let doc_arena = DocArena::default();
    println!(
        "\nLOWER\n\n{}",
        mir.to_doc(&doc_arena).pretty_string(PRETTY_WIDTH)
    );

    shrink::shrink(&mut mir);
    println!(
        "\nSHRINK\n\n{}",
        mir.to_doc(&doc_arena).pretty_string(PRETTY_WIDTH)
    );

    closure_convert::convert(&mut mir);
    println!(
        "\nCLOSURE\n\n{}",
        mir.to_doc(&doc_arena).pretty_string(PRETTY_WIDTH)
    );

    mir
}
