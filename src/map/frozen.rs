use std::hash::{BuildHasher, Hash};

use bumpalo::Bump;
use hashbrown::{
    hash_map::{RawEntryBuilder, RawEntryBuilderMut, RawEntryMut},
    Equivalent,
};

/// A view into a bumpalo-backed [`hashbrown::HashMap`] that prevent insertions and removals,
/// but can be sent between threads safely.
pub struct FrozenMap<'a, 'bump, K, V, S>(&'a mut hashbrown::HashMap<K, V, S, &'bump Bump>);

/// SAFETY:
///
/// - K, V, S are [`Send`]
/// - The FrozenMap never reallocates.
/// - The FrozenMap does not leak a shared reference to the allocator **or its inner hashmap**.
///
/// So, it is safe to send the contained shared reference to the allocator
unsafe impl<K, V, S> Send for FrozenMap<'_, '_, K, V, S>
where
    K: Send,
    V: Send,
    S: Send,
{
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

    /// An iterator visiting all values in arbitrary order. The iterator element type is `&'a V``.
    #[inline]
    pub fn values(&self) -> hashbrown::hash_map::Values<'_, K, V> {
        self.0.values()
    }

    /// An iterator visiting all values mutably in arbitrary order. The iterator element type is `&'a mut V`.
    #[inline]
    pub fn values_mut(&mut self) -> hashbrown::hash_map::ValuesMut<'_, K, V> {
        self.0.values_mut()
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The iterator element type is `(&'a K, &'a V)`.
    #[inline]
    pub fn iter(&self) -> hashbrown::hash_map::Iter<'_, K, V> {
        self.0.iter()
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with mutable references to the values. The iterator element type is `(&'a K, &'a mut V)`.
    #[inline]
    pub fn iter_mut(&mut self) -> hashbrown::hash_map::IterMut<'_, K, V> {
        self.0.iter_mut()
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
    /// Returns a reference to the value corresponding to the key.
    #[inline]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.0.get(key)
    }

    /// Returns the key-value pair corresponding to the supplied key.
    #[inline]
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.0.get_key_value(key)
    }

    /// Returns the key-value pair corresponding to the supplied key, with a mutable reference to value.
    #[inline]
    pub fn get_key_value_mut<Q>(&mut self, key: &Q) -> Option<(&K, &mut V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.0.get_key_value_mut(key)
    }

    /// Returns `true` if the map contains a value for the specified key.
    #[inline]
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.0.contains_key(key)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    #[inline]
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.0.get_mut(key)
    }

    /// Attempts to get mutable references to `N` values in the map at once.
    ///
    /// Returns an array of length `N` with the results of each query.
    /// For soundness, at most one mutable reference will be returned to any value. `None` will be used if the key is missing.
    ///
    /// # Panics
    ///
    /// Panics if any keys are overlapping.
    #[inline]
    pub fn get_many_mut<Q, const N: usize>(&mut self, ks: [&Q; N]) -> [Option<&mut V>; N]
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.0.get_many_mut(ks)
    }

    /// Attempts to get mutable references to `N` values in the map at once, without validating that the values are unique.
    ///
    /// Returns an array of length `N` with the results of each query. `None` will be used if the key is missing.
    ///
    /// For a safe alternative see [`Self::get_many_mut`].
    ///
    /// # Safety
    ///
    /// Calling this method with overlapping keys is undefined behavior even if the resulting references are not used.
    #[inline]
    pub unsafe fn get_many_unchecked_mut<Q, const N: usize>(
        &mut self,
        ks: [&Q; N],
    ) -> [Option<&mut V>; N]
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        unsafe { self.0.get_many_unchecked_mut(ks) }
    }

    /// Attempts to get mutable references to `N` values in the map at once, with immutable references to the corresponding keys.
    ///
    /// Returns an array of length `N` with the results of each query.
    /// For soundness, at most one mutable reference will be returned to any value.
    /// `None` will be used if the key is missing.
    ///
    /// # Panics
    ///
    /// Panics if any keys are overlapping.
    #[inline]
    pub fn get_many_key_value_mut<Q, const N: usize>(
        &mut self,
        ks: [&Q; N],
    ) -> [Option<(&K, &mut V)>; N]
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        self.0.get_many_key_value_mut(ks)
    }

    /// Attempts to get mutable references to `N` values in the map at once,
    /// with immutable references to the corresponding keys,
    /// without validating that the values are unique.
    ///
    /// Returns an array of length `N` with the results of each query.
    /// `None`` will be returned if any of the keys are missing.
    ///
    /// For a safe alternative see [`Self::get_many_key_value_mut`].
    ///
    /// # Safety
    ///
    /// Calling this method with overlapping keys is undefined behavior even if the resulting references are not used.
    #[inline]
    pub unsafe fn get_many_key_value_unchecked_mut<Q, const N: usize>(
        &mut self,
        ks: [&Q; N],
    ) -> [Option<(&K, &mut V)>; N]
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        unsafe { self.0.get_many_key_value_unchecked_mut(ks) }
    }
}

impl<'bump, K, V, S> FrozenMap<'_, 'bump, K, V, S> {
    /// Creates a raw immutable entry builder for the map.
    ///
    /// Raw entries provide the lowest level of control for searching and manipulating a map. They must be manually initialized with a hash and then manually searched.
    ///
    /// This is useful for
    ///
    /// - Hash memoization
    /// - Using a search key that doesn't work with the [`std::borrow::Borrow`] trait
    /// - Using custom comparison logic without newtype wrappers
    /// - Unless you are in such a situation, higher-level and more foolproof APIs like [`Self::get`] should be preferred.
    ///
    /// If you need to mutate values through entries, consider [`Self::raw_entry_mut`].
    #[inline]
    pub fn raw_entry(&self) -> RawEntryBuilder<'_, K, V, S, &'bump Bump> {
        self.0.raw_entry()
    }

    /// Creates a raw entry builder for the map.
    ///
    /// Raw entries provide the lowest level of control for searching and manipulating a map.
    /// They must be manually initialized with a hash and then manually searched.
    ///
    /// Raw entries are useful for such exotic situations as:
    ///
    /// - Hash memoization
    /// - Using a search key that doesn't work with the [`std::borrow::Borrow`] trait
    /// - Using custom comparison logic without newtype wrappers
    ///
    /// Because raw entries provide much more low-level control, it's much easier to put the `HashMap` into an inconsistent state which, while memory-safe, will cause the map to produce seemingly random results.
    /// Higher-level and more foolproof APIs like `entry` should be preferred when possible.
    ///
    /// In particular, the hash used to initialized the raw entry must still be consistent with the hash of the key that is ultimately stored in the entry.
    #[inline]
    pub fn raw_entry_mut(&mut self) -> FrozenRawEntryBuilderMut<'_, 'bump, K, V, S> {
        FrozenRawEntryBuilderMut(self.0.raw_entry_mut())
    }
}

/// A builder for computing where in a `HashMap` a key-value pair would be stored.
///
/// See the [`hashbrown::HashMap::raw_entry_mut`] docs for usage examples.
pub struct FrozenRawEntryBuilderMut<'a, 'bump, K, V, S>(
    RawEntryBuilderMut<'a, K, V, S, &'bump Bump>,
);

impl<'a, K, V, S> FrozenRawEntryBuilderMut<'a, '_, K, V, S> {
    /// Creates a [`FrozenRawEntryBuilderMut`] from the given key.
    #[allow(clippy::wrong_self_convention)] // blame hashbrown
    #[inline]
    pub fn from_key<Q>(self, k: &Q) -> Option<(&'a K, &'a mut V)>
    where
        S: BuildHasher,
        Q: Hash + Equivalent<K> + ?Sized,
    {
        match self.0.from_key(k) {
            RawEntryMut::Occupied(raw_occupied_entry_mut) => {
                let (k, v) = raw_occupied_entry_mut.into_key_value();
                Some((k, v))
            }
            RawEntryMut::Vacant(_) => None,
        }
    }

    /// Accesses a mutable entry from the given key and its hash.
    #[allow(clippy::wrong_self_convention)] // blame hashbrown
    #[inline]
    pub fn from_key_hashed_nocheck<Q>(self, hash: u64, k: &Q) -> Option<(&'a K, &'a mut V)>
    where
        Q: Equivalent<K> + ?Sized,
    {
        match self.0.from_key_hashed_nocheck(hash, k) {
            RawEntryMut::Occupied(raw_occupied_entry_mut) => {
                let (k, v) = raw_occupied_entry_mut.into_key_value();
                Some((k, v))
            }
            RawEntryMut::Vacant(_) => None,
        }
    }

    /// Accesses a mutable entry from the given hash and matching function.
    #[allow(clippy::wrong_self_convention)] // blame hashbrown
    #[inline]
    pub fn from_hash<F>(self, hash: u64, is_match: F) -> Option<(&'a K, &'a mut V)>
    where
        for<'b> F: FnMut(&'b K) -> bool,
    {
        match self.0.from_hash(hash, is_match) {
            RawEntryMut::Occupied(raw_occupied_entry_mut) => {
                let (k, v) = raw_occupied_entry_mut.into_key_value();
                Some((k, v))
            }
            RawEntryMut::Vacant(_) => None,
        }
    }
}
