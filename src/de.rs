use bumpalo::Bump;
use serde::de::{DeserializeSeed, Visitor};

/// A type that can be used as a [`DeserializeSeed`] to deserialize strings that are
/// either allocated into a [`Bump`] or reference the source data.
pub struct BumpStrSeed<'bump>(pub &'bump Bump);

impl<'de, 'bump: 'de> DeserializeSeed<'de> for BumpStrSeed<'bump> {
    type Value = &'de str;

    #[inline]
    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct BumpVisitor<'bump>(&'bump Bump);
        impl<'de, 'bump: 'de> Visitor<'de> for BumpVisitor<'bump> {
            type Value = &'de str;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(formatter, "expecting a string")
            }
            fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(v)
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(self.0.alloc_str(v))
            }
        }
        deserializer.deserialize_str(BumpVisitor(self.0))
    }
}
