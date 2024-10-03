use serde_json::value::RawValue;

use crate::RawMap;

/// An iterator over the keys of a [`RawMap`].
///
/// Iterates in first-insertion order.
pub struct Keys<'bump, 'a>(std::slice::Iter<'a, (&'bump str, &'bump RawValue)>);
impl<'a, 'bump> Iterator for Keys<'bump, 'a> {
    type Item = &'bump str;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.0)
    }
}

/// An iterator over the values of a [`RawMap`].
///
/// Iterates in first-insertion order.
pub struct Values<'bump, 'a>(std::slice::Iter<'a, (&'bump str, &'bump RawValue)>);
impl<'a, 'bump> Iterator for Values<'bump, 'a> {
    type Item = &'bump RawValue;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        Some(self.0.next()?.1)
    }
}

/// An iterator over the (key, value) pairs of a [`RawMap`].
///
/// Iterates in first-insertion order.
pub struct Iter<'bump, 'a>(std::slice::Iter<'a, (&'bump str, &'bump RawValue)>);
impl<'bump, 'a> Iterator for Iter<'bump, 'a> {
    type Item = (&'bump str, &'bump RawValue);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, v)| (*k, *v))
    }
}

impl<'bump> IntoIterator for RawMap<'bump> {
    type Item = (&'bump str, &'bump RawValue);

    type IntoIter = IntoIter<'bump>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.data.into_iter())
    }
}

/// An owning iterator over the values of a [`RawMap`].
///
/// Iterates in first-insertion order.
pub struct IntoIter<'bump>(
    bumpalo::collections::vec::IntoIter<'bump, (&'bump str, &'bump RawValue)>,
);
impl<'bump> Iterator for IntoIter<'bump> {
    type Item = (&'bump str, &'bump RawValue);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl<'bump, 'a> IntoIterator for &'a RawMap<'bump> {
    type Item = (&'bump str, &'bump RawValue);

    type IntoIter = Iter<'bump, 'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter(self.data.iter())
    }
}

impl<'bump> RawMap<'bump> {
    /// Iterates over the (key, value) pairs of the map in first-insertion order.
    #[inline]
    pub fn iter(&self) -> Iter<'bump, '_> {
        Iter(self.data.iter())
    }

    /// Iterates over the keys of the map in first-insertion order.
    #[inline]
    pub fn keys(&self) -> Keys<'bump, '_> {
        Keys(self.data.iter())
    }

    /// Iterates over the values of the map in first-insertion order
    #[inline]
    pub fn values(&self) -> Values<'bump, '_> {
        Values(self.data.iter())
    }
}
