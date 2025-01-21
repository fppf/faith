/// Union-find implementation from [ena](https://docs.rs/ena).
use base::index::Idx;

pub trait UnifyKey: Idx {
    type Value: UnifyValue;

    /// You should return first the key that should be used as root,
    /// then the other key (that will then point to the new root).
    ///
    /// NB. The only reason to implement this method is if you want to
    /// control what value is returned from `find()`. In general, it
    /// is better to let the unification table determine the root,
    /// since overriding the rank can cause execution time to increase
    /// dramatically.
    #[allow(unused_variables)]
    fn order_roots(
        a: Self,
        a_value: &Self::Value,
        b: Self,
        b_value: &Self::Value,
    ) -> Option<(Self, Self)> {
        None
    }
}

pub trait UnifyValue: Clone {
    type Error;

    fn unify_values(lhs: &Self, rhs: &Self) -> Result<Self, Self::Error>;
}

impl UnifyValue for () {
    type Error = !;

    fn unify_values(_: &Self, _: &Self) -> Result<Self, Self::Error> {
        Ok(())
    }
}

struct VarValue<K: UnifyKey> {
    parent: K,
    value: K::Value,
    rank: u32,
}

impl<K: UnifyKey> VarValue<K> {
    fn new_var(key: K, value: K::Value) -> Self {
        Self {
            parent: key,
            value,
            rank: 0,
        }
    }

    fn redirect(&mut self, to: K) {
        self.parent = to;
    }

    fn root(&mut self, rank: u32, value: K::Value) {
        self.rank = rank;
        self.value = value;
    }
}

pub struct UnificationTable<K: UnifyKey> {
    values: Vec<VarValue<K>>,
}

impl<K: UnifyKey> Default for UnificationTable<K> {
    fn default() -> Self {
        Self { values: Vec::new() }
    }
}

impl<K: UnifyKey> UnificationTable<K> {
    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn new_key(&mut self, value: K::Value) -> K {
        let key = <K as Idx>::new(self.len());
        self.values.push(VarValue::new_var(key, value));
        key
    }

    /// Given two keys, indicates whether they have been unioned together.
    #[allow(unused)]
    pub fn unioned(&mut self, key_a: K, key_b: K) -> bool {
        self.find(key_a) == self.find(key_b)
    }

    /// Given a key, returns the (current) root key.
    pub fn find(&mut self, key: K) -> K {
        self.uninlined_get_root_key(key)
    }

    /// Unions together two variables, merging their values. If merging the values fails, the error
    /// is propogates and this method has no effect.
    pub fn unify_var_var(
        &mut self,
        key_a: K,
        key_b: K,
    ) -> Result<(), <<K as UnifyKey>::Value as UnifyValue>::Error> {
        let root_a = self.uninlined_get_root_key(key_a);
        let root_b = self.uninlined_get_root_key(key_b);

        if root_a == root_b {
            return Ok(());
        }

        let combined =
            K::Value::unify_values(&self.value(root_a).value, &self.value(root_b).value)?;
        self.unify_roots(root_a, root_b, combined);
        Ok(())
    }

    /// Set the value of the key `key_a` to `value_b`, attempting to merge with the previous value.
    pub fn unify_var_value(
        &mut self,
        key_a: K,
        value_b: K::Value,
    ) -> Result<(), <<K as UnifyKey>::Value as UnifyValue>::Error> {
        let root_a = self.uninlined_get_root_key(key_a);
        let value = K::Value::unify_values(&self.value(root_a).value, &value_b)?;
        self.update_value(root_a, |node| node.value = value);
        Ok(())
    }

    /// Returns the current value for the given key. If the key has been unioned, this will give
    /// the value from the current root.
    pub fn probe_value(&mut self, key: K) -> K::Value {
        self.inlined_probe_value(key)
    }

    #[inline(always)]
    pub fn inlined_probe_value(&mut self, key: K) -> K::Value {
        let key = self.inlined_get_root_key(key);
        self.value(key).value.clone()
    }

    fn value(&self, key: K) -> &VarValue<K> {
        &self.values[key.index()]
    }

    #[inline(always)]
    fn inlined_get_root_key(&mut self, key: K) -> K {
        let v = self.value(key);
        if v.parent == key {
            return key;
        }

        let redirect = v.parent;
        let root_key = self.uninlined_get_root_key(redirect);
        if root_key != redirect {
            self.update_value(key, |v| v.parent = root_key);
        }
        root_key
    }

    #[inline(never)]
    fn uninlined_get_root_key(&mut self, key: K) -> K {
        self.inlined_get_root_key(key)
    }

    fn update_value<F>(&mut self, key: K, f: F)
    where
        F: FnOnce(&mut VarValue<K>),
    {
        f(&mut self.values[key.index()]);
    }

    fn unify_roots(&mut self, key_a: K, key_b: K, new_value: K::Value) {
        let rank_a = self.value(key_a).rank;
        let rank_b = self.value(key_b).rank;

        if let Some((new_root, redirected)) = K::order_roots(
            key_a,
            &self.value(key_a).value,
            key_b,
            &self.value(key_b).value,
        ) {
            // Compute the new rank for the new root that they chose;
            // this may not be the optimal choice.
            let new_rank = if new_root == key_a {
                debug_assert_eq!(redirected, key_b);
                if rank_a > rank_b { rank_a } else { rank_b + 1 }
            } else {
                debug_assert_eq!(new_root, key_b);
                debug_assert_eq!(redirected, key_a);
                if rank_b > rank_a { rank_b } else { rank_a + 1 }
            };
            self.redirect_root(new_rank, redirected, new_root, new_value);
        } else if rank_a > rank_b {
            // a has greater rank, so a should become b's parent
            // (b redirects to a).
            self.redirect_root(rank_a, key_b, key_a, new_value);
        } else if rank_a < rank_b {
            // b has greater rank, so a should redirect to b.
            self.redirect_root(rank_b, key_a, key_b, new_value);
        } else {
            // If equal, redirect one to the other and increment the other's rank.
            self.redirect_root(rank_a + 1, key_a, key_b, new_value);
        }
    }

    // Internal method to redirect `old_root_key` (which is currently a root) to a child of
    // `new_root_key` (which will remain a root). The rank and value of `new_root_key` will be
    // updated to `new_rank` and `new_value` respectively.
    fn redirect_root(
        &mut self,
        new_rank: u32,
        old_root_key: K,
        new_root_key: K,
        new_value: K::Value,
    ) {
        self.update_value(old_root_key, |old_root_value| {
            old_root_value.redirect(new_root_key);
        });
        self.update_value(new_root_key, |new_root_value| {
            new_root_value.root(new_rank, new_value);
        });
    }
}
