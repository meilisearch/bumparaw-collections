use bumpalo::Bump;
use serde::{ser::SerializeSeq, Serialize};
use serde_json::value::RawValue;

use bumpalo::collections::Vec as BVec;

mod de;
/// Contains iterator types and implementations for [`RawVec`].
pub mod iter;

/// A vector of [`RawValue`]s backed by a [`Bump`].
///
/// All allocations happen in the associated [`Bump`].
#[derive(Debug)]
pub struct RawVec<'bump>(BVec<'bump, &'bump RawValue>);

impl<'bump> Serialize for RawVec<'bump> {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for value in self {
            seq.serialize_element(value)?;
        }
        seq.end()
    }
}

impl<'bump> RawVec<'bump> {
    /// Constructs a vector from a raw value and a bump allocator.
    ///
    /// # Error
    ///
    /// - if the raw value cannot be parsed as a sequence (JSON array).
    #[inline]
    pub fn from_raw_value(
        raw: &'bump RawValue,
        bump: &'bump Bump,
    ) -> Result<Self, serde_json::Error> {
        Self::from_deserializer(raw, bump)
    }

    /// Constructs an empty vector backed by the specified bump allocator.
    #[inline]
    pub fn new_in(bump: &'bump Bump) -> Self {
        Self(BVec::new_in(bump))
    }

    /// Inserts an element at position `index` within the vector, shifting all elements after it to the right.
    ///
    /// # Panics
    ///
    /// - if `index > len`.
    #[inline]
    pub fn insert(&mut self, index: usize, value: &'bump RawValue) {
        self.0.insert(index, value);
    }

    /// Appends an element to the back of a vector.
    #[inline]
    pub fn push(&mut self, value: &'bump RawValue) {
        self.0.push(value);
    }

    /// Returns a reference to an element, or `None` if out of bounds.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&'bump RawValue> {
        self.0.get(index).copied()
    }

    /// The number of elements in the vector, also referred to as its 'length'.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// `true` if the vector contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Reserves capacity for at least additional more elements to be inserted in the vector.
    ///
    /// # Panics
    ///
    /// - if the new capacity overflows `usize`.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional);
    }

    /// Consumes `self` and returns its inner representation as a slice.
    #[inline]
    pub fn into_bump_slice(self) -> &'bump [&'bump RawValue] {
        self.0.into_bump_slice()
    }
}
