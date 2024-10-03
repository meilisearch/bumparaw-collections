use serde_json::value::RawValue;

use crate::RawVec;

/// An iterator over the values of a [`RawVec`].
pub struct Iter<'bump, 'a>(std::slice::Iter<'a, &'bump RawValue>);
impl<'bump, 'a> Iterator for Iter<'bump, 'a> {
    type Item = &'bump RawValue;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().copied()
    }
}

impl<'bump> IntoIterator for RawVec<'bump> {
    type Item = &'bump RawValue;

    type IntoIter = IntoIter<'bump>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

/// An owned iterator over the values of a [`RawVec`].
pub struct IntoIter<'bump>(bumpalo::collections::vec::IntoIter<'bump, &'bump RawValue>);
impl<'bump> Iterator for IntoIter<'bump> {
    type Item = &'bump RawValue;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<'bump, 'a> IntoIterator for &'a RawVec<'bump> {
    type Item = &'bump RawValue;

    type IntoIter = Iter<'bump, 'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.iter())
    }
}

impl<'bump> RawVec<'bump> {
    /// Iterates over the value of the vector.
    #[inline]
    pub fn iter(&self) -> Iter<'bump, '_> {
        Iter(self.0.iter())
    }
}
