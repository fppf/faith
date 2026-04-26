mod closure_convert;
mod lower;
mod mir;
mod pretty;
mod shrink;

pub use mir::*;

pub use lower::lower;
pub use shrink::shrink;

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
