use bumpalo::Bump;
use hashbrown::DefaultHashBuilder;
use serde::{ser::SerializeMap, Serialize};
use serde_json::value::RawValue;

use bumpalo::collections::Vec as BVec;

mod de;
mod frozen;
/// Contains iterator types and implementations for [`RawMap`].
pub mod iter;

/// An order-preserving map optimized for iteration over insertion.
///
/// It consists in a vector containing references to *both* the keys and data, and in a hashmap
/// meant to provide constant time access to the elements.
///
/// Iteration happens in the order of insertion. If a key is inserted multiple times,
/// the associated value will be the last inserted value, but the order of iteration
/// will respect the order of the first insertion.
///
/// All allocations happen in the associated [`Bump`].
pub struct RawMap<'bump> {
    data: BVec<'bump, (&'bump str, &'bump RawValue)>,
    cache: hashbrown::HashMap<&'bump str, usize, DefaultHashBuilder, &'bump Bump>,
}

impl<'bump> Serialize for RawMap<'bump> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (key, value) in self {
            map.serialize_entry(key, value)?;
        }
        map.end()
    }
}

impl<'bump> RawMap<'bump> {
    /// Constructs a map from a raw value and a bump allocator.
    ///
    /// # Errors
    ///
    /// - if the raw value cannot be parsed as a map (JSON object).
    #[inline]
    pub fn from_raw_value(
        raw: &'bump RawValue,
        bump: &'bump Bump,
    ) -> Result<Self, serde_json::Error> {
        Self::from_deserializer(raw, bump)
    }

    /// Constructs an empty map backed by the specified bump allocator.
    #[inline]
    pub fn new_in(bump: &'bump Bump) -> Self {
        Self {
            data: BVec::new_in(bump),
            cache: hashbrown::HashMap::new_in(bump),
        }
    }

    /// Inserts a new (key, value) pair in the map.
    ///
    /// If the key already exists, then the order of the first insertion of the key is maintained, the value is updated,
    /// and the previous value is returned.
    #[inline]
    pub fn insert(&mut self, key: &'bump str, value: &'bump RawValue) -> Option<&'bump RawValue> {
        match self.cache.entry(key) {
            hashbrown::hash_map::Entry::Occupied(entry) => {
                let index = entry.get();
                Some(std::mem::replace(
                    &mut self.data.get_mut(*index).unwrap().1,
                    value,
                ))
            }
            hashbrown::hash_map::Entry::Vacant(entry) => {
                let index = self.data.len();
                self.data.push((key, value));
                entry.insert(index);
                None
            }
        }
    }

    /// Retrieves the value associated with a key, if present.
    #[inline]
    pub fn get(&self, key: &str) -> Option<&'bump RawValue> {
        let index = self.cache.get(key)?;
        self.data.get(*index).map(|(_, v)| *v)
    }

    /// Retrieves the index of a key in the data slice, if present.
    #[inline]
    pub fn get_index(&self, key: &str) -> Option<usize> {
        self.cache.get(key).copied()
    }

    /// The number of elements in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// `true` if there are no elements in the map.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Reserves capacity for at least additional more elements to be inserted in the map.
    ///
    /// # Panics
    ///
    /// - if the new capacity exceeds [`isize::MAX`].
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.data.reserve(additional);
        self.cache.reserve(additional);
    }

    /// Returns the underlying vec as a slice.
    #[inline]
    pub fn as_slice(&self) -> &[(&'bump str, &'bump RawValue)] {
        self.data.as_slice()
    }

    /// Consumes `self` and returns the underlying vec.
    #[inline]
    pub fn into_vec(self) -> BVec<'bump, (&'bump str, &'bump RawValue)> {
        self.data
    }

    /// Consumes `self` and returns the underlying vec as a bump slice.
    #[inline]
    pub fn into_bump_slice(self) -> &'bump [(&'bump str, &'bump RawValue)] {
        self.data.into_bump_slice()
    }

    /// Makes this map [`Send`] by forbidding any future modifications.
    #[inline]
    pub fn freeze(&mut self) -> FrozenRawMap<'_, 'bump> {
        FrozenRawMap::new(self)
    }
}

/// A view into a [`RawMap`] that prevents insertions, but can be sent between threads safely.
pub struct FrozenRawMap<'a, 'bump> {
    data: &'a [(&'bump str, &'bump RawValue)],
    cache: frozen::FrozenMap<'a, 'bump, &'bump str, usize, DefaultHashBuilder>,
}

impl<'a, 'bump> FrozenRawMap<'a, 'bump> {
    /// Makes the passed map [`Send`] by preventing any future modifications.
    #[inline]
    pub fn new(map: &'a mut RawMap<'bump>) -> Self {
        FrozenRawMap {
            data: map.data.as_slice(),
            cache: frozen::FrozenMap::new(&mut map.cache),
        }
    }

    /// Retrieves the value associated with a key, if present.
    #[inline]
    pub fn get(&self, key: &str) -> Option<&'bump RawValue> {
        let index = self.cache.get(key)?;
        self.data.get(*index).map(|(_, v)| *v)
    }

    /// Retrieves the index of a key in the data slice, if present.
    #[inline]
    pub fn get_index(&self, key: &str) -> Option<usize> {
        self.cache.get(key).copied()
    }

    /// The number of elements in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// `true` if there are no elements in the map.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Returns a reference to the underlying slice.
    #[inline]
    pub fn as_slice(&self) -> &'a [(&'bump str, &'bump RawValue)] {
        self.data
    }
}

pub use frozen::FrozenMap;
pub use frozen::FrozenRawEntryBuilderMut;
