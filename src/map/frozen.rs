use std::{fmt, hash::Hash};

use bumpalo::Bump;
use hashbrown::Equivalent;

use crate::frozen::Freezable;

/// A view into a bumpalo-backed [`hashbrown::HashMap`] that prevent insertions and removals,
/// but can be sent between threads safely.
pub struct FrozenMap<'a, 'bump, K, V, S>(&'a mut hashbrown::HashMap<K, V, S, &'bump Bump>);

/// SAFETY:
///
/// - K, V::Frozen, S are [`Send`]
/// - The FrozenMap never gives access to raw `V`, only `V::Frozen`.
/// - The FrozenMap never reallocates.
/// - The FrozenMap does not leak a shared reference to the allocator **or its inner hashmap**.
///
/// So, it is safe to send the contained shared reference to the allocator
unsafe impl<'aa, 'a: 'aa, K, V, S> Send for FrozenMap<'a, '_, K, V, S>
where
    K: Send,
    V: Freezable<'aa>,
    S: Send,
{
}

impl<'aa, 'a: 'aa, 'bump, K, V, S> FrozenMap<'a, 'bump, K, V, S>
where
    V: Freezable<'aa>,
{
    /// An iterator visiting all values mutably in arbitrary order. The iterator element type is `V::Frozen`.
    #[inline]
    pub fn values_mut(&'aa mut self) -> impl Iterator<Item = V::Frozen> {
        self.0.values_mut().map(|v| v.freeze())
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with mutable references to the values. The iterator element type is `(&'a K, V::Frozen)`.
    #[inline]
    pub fn iter_mut(&'aa mut self) -> impl Iterator<Item = (&'aa K, V::Frozen)> {
        self.0.iter_mut().map(|(k, v)| (k, v.freeze()))
    }
}

impl<'a, 'bump, K, V, S> FrozenMap<'a, 'bump, K, V, S> {
    /// Makes the passed map [`Send`] by preventing any future modifications.
    #[inline]
    pub fn new(map: &'a mut hashbrown::HashMap<K, V, S, &'bump Bump>) -> Self {
        Self(map)
    }

    /// Returns the number of elements the map can hold without reallocating.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element type is `&'a K`.
    #[inline]
    pub fn keys(&self) -> hashbrown::hash_map::Keys<'_, K, V> {
        self.0.keys()
    }

    /// Returns the number of elements in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the map contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<K, V, S> FrozenMap<'_, '_, K, V, S>
where
    K: Eq + Hash,
    S: std::hash::BuildHasher,
{
    /// Returns `true` if the map contains a value for the specified key.
    #[inline]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.0.contains_key(key)
    }
}

impl<'aa, 'a: 'aa, K, V, S> FrozenMap<'a, '_, K, V, S>
where
    K: Eq + Hash,
    S: std::hash::BuildHasher,
    V: Freezable<'aa>,
{
    /// Returns the key-value pair corresponding to the supplied key, with a mutable reference to value.
    #[inline]
    pub fn get_key_value_mut<Q>(&'aa mut self, key: &Q) -> Option<(&'aa K, V::Frozen)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.0.get_key_value_mut(key).map(|(k, v)| (k, v.freeze()))
    }

    /// Returns a mutable reference to the value corresponding to the key.
    #[inline]
    pub fn get_mut<Q>(&'aa mut self, key: &Q) -> Option<V::Frozen>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.0.get_mut(key).map(|v| v.freeze())
    }
}

impl<K: fmt::Debug, V: fmt::Debug, S> fmt::Debug for FrozenMap<'_, '_, K, V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // technically a debug impl of V could break our assumptions about V
        f.debug_tuple("FrozenMap").field(&self.0).finish()
    }
}
