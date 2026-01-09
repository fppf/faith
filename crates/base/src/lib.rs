#![allow(clippy::mut_from_ref)] // Arena allocators are one place where this pattern is fine.
#![deny(unsafe_op_in_unsafe_fn)]
// Per the Rustonomicon:
// The precise rules that govern drop checking may be less restrictive in the future.
// The current drop check analysis is deliberately conservative and trivial; it forces
// all borrowed data in a value to outlive that value, which is certainly sound.
// Future versions of the language may make the analysis more precise, to reduce the
// number of cases where sound code is rejected as unsafe.
// In the meantime, there is an unstable attribute `may_dangle` that one can use to
// assert (unsafely) that a generic type's destructor is guaranteed to not access any
// expired data, even if its type gives it the capability to do so.
#![feature(dropck_eyepatch)]
#![feature(never_type)]
pub mod arena;
pub mod hash;
pub mod index;
pub mod pp;
pub mod unify;

pub use smallvec;
