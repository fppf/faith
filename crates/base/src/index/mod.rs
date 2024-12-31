//! Index newtypes for an indexed `Vec`.
//!
//! Taken from [`rustc_index`](https://doc.rust-lang.org/stable/nightly-rustc/rustc_index).
use std::{fmt, hash::Hash};

mod slice;
mod vec;

pub use slice::IndexSlice;
pub use vec::IndexVec;

/// Represents some newtyped `usize` wrapper.
///
/// Purpose: avoid mixing indices for different bitvector domains.
pub trait Idx: Copy + 'static + PartialEq + Eq + Hash + fmt::Debug {
    fn new(idx: usize) -> Self;

    fn index(self) -> usize;

    #[inline]
    #[must_use]
    fn plus(self, amount: usize) -> Self {
        Self::new(self.index() + amount)
    }
}

impl Idx for usize {
    #[inline]
    fn new(idx: usize) -> Self {
        idx
    }

    #[inline]
    fn index(self) -> usize {
        self
    }
}

impl Idx for u32 {
    #[inline]
    fn new(idx: usize) -> Self {
        assert!(idx <= u32::MAX as usize);
        idx as u32
    }

    #[inline]
    fn index(self) -> usize {
        self as usize
    }
}

/// Creates a struct type `$name` that implements `Idx`,
/// internally represented by a `u32`.
#[macro_export]
macro_rules! newtype_index {
    (
        $(#[$attrs:meta])*
        $vis:vis struct $name:ident {}
    ) => {
        $(#[$attrs])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        $vis struct $name {
            raw: u32,
        }

        impl $name {
            $vis const ZERO: Self = Self::from_u32(0);

            #[inline]
            $vis const fn from_usize(value: usize) -> Self {
                assert!(value <= u32::MAX as usize);
                unsafe {
                    Self::from_u32_unchecked(value as u32)
                }
            }

            #[inline]
            $vis const fn from_u32(value: u32) -> Self {
                assert!(value <= u32::MAX);
                unsafe {
                    Self::from_u32_unchecked(value)
                }
            }

            #[inline]
            $vis const unsafe fn from_u32_unchecked(value: u32) -> Self {
                Self { raw: value }
            }

            #[inline]
            $vis const fn index(self) -> usize {
                self.as_usize()
            }

            #[inline]
            $vis const fn as_u32(self) -> u32 {
                self.raw
            }

            #[inline]
            $vis const fn as_usize(self) -> usize {
                self.as_u32() as usize
            }
        }

        impl $crate::index::Idx for $name {
            #[inline]
            fn new(value: usize) -> Self {
                Self::from_usize(value)
            }

            #[inline]
            fn index(self) -> usize {
                self.as_usize()
            }
        }

        impl From<$name> for u32 {
            #[inline]
            fn from(v: $name) -> Self {
                v.as_u32()
            }
        }

        impl From<$name> for usize {
            #[inline]
            fn from(v: $name) -> Self {
                v.as_usize()
            }
        }

        impl From<u32> for $name {
            #[inline]
            fn from(value: u32) -> Self {
                Self::from_u32(value)
            }
        }

        impl From<usize> for $name {
            #[inline]
            fn from(value: usize) -> Self {
                Self::from_usize(value)
            }
        }

        impl std::ops::Add<usize> for $name {
            type Output = Self;

            #[inline]
            fn add(self, rhs: usize) -> Self::Output {
                Self::from_usize(self.index() + rhs)
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({})", stringify!($name), self.index())
            }
        }

        /*
        impl std::iter::Step for $name {
            #[inline]
            fn steps_between(start: &Self, end: &Self) -> Option<usize> {
                <usize as std::iter::Step>::steps_between(
                    &Self::index(*start),
                    &Self::index(*end),
                )
            }

            #[inline]
            fn forward_checked(start: Self, count: usize) -> Option<Self> {
                Self::index(start).checked_add(count).map(Self::from_usize)
            }

            #[inline]
            fn backward_checked(start: Self, count: usize) -> Option<Self> {
                Self::index(start).checked_sub(count).map(Self::from_usize)
            }
        }
        */
    }
}
