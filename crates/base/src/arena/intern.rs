use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::Deref,
    ptr,
};

mod private {
    #[derive(Clone, Copy, Debug)]
    pub struct PrivateZst;
}

/// Taken from `rustc_data_structures`.
///
/// A reference to a value that is interned, and is known to be unique.
///
/// Note that it is possible to have a `T` and a `Interned<T>` that are (or
/// refer to) equal but different values. But if you have two different
/// `Interned<T>`s, they both refer to the same value, at a single location in
/// memory. This means that equality and hashing can be done on the value's
/// address rather than the value's contents, which can improve performance.
///
/// The `PrivateZst` field means you can pattern match with `Interned(v, _)`
/// but you can only construct a `Interned` with `new_unchecked`, and not
/// directly.
pub struct Interned<'a, T>(pub &'a T, pub private::PrivateZst);

impl<'a, T> Interned<'a, T> {
    /// Create a new `Interned` value. The value referred to *must* be interned
    /// and thus be unique, and it *must* remain unique in the future. This
    /// function has `_unchecked` in the name but is not `unsafe`, because if
    /// the uniqueness condition is violated condition it will cause incorrect
    /// behaviour but will not affect memory safety.
    #[inline]
    pub const fn new_unchecked(t: &'a T) -> Self {
        Interned(t, private::PrivateZst)
    }
}

impl<T> Clone for Interned<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Interned<'_, T> {}

impl<T> Deref for Interned<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<T> PartialEq for Interned<'_, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Pointer equality implies equality, due to the uniqueness constraint.
        ptr::eq(self.0, other.0)
    }
}

impl<T> Eq for Interned<'_, T> {}

impl<'a, T: PartialOrd> PartialOrd for Interned<'a, T> {
    fn partial_cmp(&self, other: &Interned<'a, T>) -> Option<Ordering> {
        // Pointer equality implies equality, due to the uniqueness constraint,
        // but the contents must be compared otherwise.
        if ptr::eq(self.0, other.0) {
            Some(Ordering::Equal)
        } else {
            let res = self.0.partial_cmp(other.0);
            debug_assert_ne!(res, Some(Ordering::Equal));
            res
        }
    }
}

impl<'a, T: Ord> Ord for Interned<'a, T> {
    fn cmp(&self, other: &Interned<'a, T>) -> Ordering {
        // Pointer equality implies equality, due to the uniqueness constraint,
        // but the contents must be compared otherwise.
        if ptr::eq(self.0, other.0) {
            Ordering::Equal
        } else {
            let res = self.0.cmp(other.0);
            debug_assert_ne!(res, Ordering::Equal);
            res
        }
    }
}

impl<T> Hash for Interned<'_, T> {
    #[inline]
    fn hash<H: Hasher>(&self, s: &mut H) {
        // Pointer hashing is sufficient, due to the uniqueness constraint.
        ptr::hash(self.0, s)
    }
}

impl<T: fmt::Debug> fmt::Debug for Interned<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}
