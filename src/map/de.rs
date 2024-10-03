use bumpalo::Bump;
use serde::{de::Visitor, Deserializer};
use serde_json::value::RawValue;

use crate::{de::BumpStrSeed, RawMap};

pub struct BumpRawMapVisitor<'bump>(&'bump Bump);

impl<'bump> Visitor<'bump> for BumpRawMapVisitor<'bump> {
    type Value = RawMap<'bump>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a map")
    }

    #[inline]
    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'bump>,
    {
        let mut top = RawMap::new_in(self.0);

        if let Some(size_hint) = map.size_hint() {
            top.reserve(size_hint);
        }
        while let Some(key) = map.next_key_seed(BumpStrSeed(self.0))? {
            let value: &'bump RawValue = map.next_value()?;
            top.insert(key, value);
        }
        Ok(top)
    }

    #[inline]
    fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'bump>,
    {
        deserializer.deserialize_map(self)
    }
}

impl<'bump> RawMap<'bump> {
    /// Constructs a new map from a [`Deserializer`].
    ///
    /// # Errors
    ///
    /// - the data does not deserializes as a map.
    #[inline]
    pub fn from_deserializer<D>(deserializer: D, bump: &'bump Bump) -> Result<Self, D::Error>
    where
        D: Deserializer<'bump>,
    {
        deserializer.deserialize_map(BumpRawMapVisitor(bump))
    }
}
