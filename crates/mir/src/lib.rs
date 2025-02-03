#![feature(let_chains)]
#![allow(unused)]

mod lower;
mod match_compile;
mod mir;
mod pretty;

pub use mir::*;

pub use lower::lower;

// Idea for MIR
// After typechecking of HIR, we want a smaller (still-typed) language
// that we can use for latter passes.
//
// Want:
//   - No modules -> everything is a sequence of declarations
//   - Likewise, all paths are lowered to unique labels (integers)
//   - Unpack all patterns into simple bindings (i.e., let (x, y) = (1, 2), z = 3 in e becomes let x = 1 in let y = 2 in let z = 3 in e)
//   - Linearize expresssions, convert to ANF form.
//   - Desugar surface language constructs, such as sequence (;) to let statement
//   - Pattern matches should be compiled to decision trees at this point (done during inference)
