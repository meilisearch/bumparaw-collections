use bumpalo::Bump;
use serde::{de::Visitor, Deserializer};
use serde_json::value::RawValue;

use crate::RawVec;

pub struct BumpRawArrayVisitor<'bump>(&'bump Bump);

impl<'bump> Visitor<'bump> for BumpRawArrayVisitor<'bump> {
    type Value = RawVec<'bump>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a sequence")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'bump>,
    {
        let mut raw = RawVec::new_in(self.0);

        if let Some(size_hint) = seq.size_hint() {
            raw.reserve(size_hint);
        }
        while let Some(value) = seq.next_element()? {
            let value: &'bump RawValue = value;
            raw.push(value);
        }
        Ok(raw)
    }
}

impl<'bump> RawVec<'bump> {
    /// Constructs a vector from the data of a [`Deserializer`].
    ///
    /// # Errors
    ///
    /// - the data cannot be deserialized as an array.
    #[inline]
    pub fn from_deserializer<D>(deserializer: D, bump: &'bump Bump) -> Result<Self, D::Error>
    where
        D: Deserializer<'bump>,
    {
        deserializer.deserialize_seq(BumpRawArrayVisitor(bump))
    }
}
