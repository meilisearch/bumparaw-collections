use std::hash::BuildHasher;

use bumpalo::Bump;
use hashbrown::DefaultHashBuilder;
use serde::de::Deserializer as _;
use serde::de::Visitor;

use serde_json::value::RawValue;

/// Represents a partially parsed JSON value referencing the underlying data.
#[derive(Debug)]
pub enum Value<'bump, S = DefaultHashBuilder> {
    /// A JSON null value.
    Null,
    /// A JSON boolean.
    Bool(bool),
    /// A JSON number.
    Number(Number),
    /// A JSON string.
    String(&'bump str),
    /// A JSON array.
    Array(crate::RawVec<'bump>),
    /// A JSON object.
    Object(crate::RawMap<'bump, S>),
}

#[derive(Debug)]
/// A JSON number
pub enum Number {
    /// Positive JSON number up to [`u64::MAX`]
    PosInt(u64),
    /// Negative JSON number down to [`i64::MIN`]
    NegInt(i64),
    /// Any other JSON number
    Finite(f64),
}

impl<'de, 'bump: 'de> Value<'de> {
    /// Constructs a value by parsing the top level of a [`serde_json::value::RawValue`].
    ///
    /// The resulting value will refer to the underlying JSON data as much as possible.
    /// Any allocation that needs to occur (e.g., map nodes or escaped strings) will take place in the
    /// provided [`bumpalo::Bump`].
    pub fn from_raw_value(
        raw: &'de RawValue,
        bump: &'bump Bump,
    ) -> Result<Value<'de>, serde_json::Error> {
        raw.deserialize_any(ValueVisitor {
            bump,
            hash_builder: DefaultHashBuilder::default(),
        })
    }
}

impl<'de, 'bump: 'de, S: BuildHasher> Value<'de, S> {
    /// Constructs a value by parsing the top level of a [`serde_json::value::RawValue`].
    ///
    /// The resulting value will refer to the underlying JSON data as much as possible.
    /// Any allocation that needs to occur (e.g., map nodes or escaped strings) will take place in the
    /// provided [`bumpalo::Bump`].
    pub fn from_raw_value_and_hasher(
        raw: &'de RawValue,
        hash_builder: S,
        bump: &'bump Bump,
    ) -> Result<Value<'de, S>, serde_json::Error> {
        raw.deserialize_any(ValueVisitor { bump, hash_builder })
    }
}

struct ValueVisitor<'bump, S> {
    bump: &'bump Bump,
    hash_builder: S,
}

impl<'de, S: BuildHasher> Visitor<'de> for ValueVisitor<'de, S> {
    type Value = Value<'de, S>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "any valid JSON value")
    }

    fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Value::Bool(v))
    }

    fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Value::Number(Number::NegInt(v)))
    }

    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Value::Number(Number::PosInt(v)))
    }

    fn visit_f64<E>(self, v: f64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(if v.is_finite() {
            Value::Number(Number::Finite(v))
        } else {
            Value::Null
        })
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        let v = self.bump.alloc_str(v);
        self.visit_borrowed_str(v)
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Value::String(v))
    }

    fn visit_none<E>(self) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Value::Null)
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let raw_value: &RawValue = serde::de::Deserialize::deserialize(deserializer)?;
        raw_value
            .deserialize_any(self)
            .map_err(serde::de::Error::custom)
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Value::Null)
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let mut array = crate::RawVec::new_in(self.bump);
        if let Some(size_hint) = seq.size_hint() {
            array.reserve(size_hint);
        }
        while let Some(next) = seq.next_element()? {
            array.push(next);
        }
        Ok(Value::Array(array))
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::MapAccess<'de>,
    {
        let mut object = crate::RawMap::with_hasher_in(self.hash_builder, self.bump);
        if let Some(size_hint) = map.size_hint() {
            object.reserve(size_hint);
        }
        while let Some(key) = map.next_key_seed(crate::de::BumpStrSeed(self.bump))? {
            let value = map.next_value()?;
            object.insert(key, value);
        }
        Ok(Value::Object(object))
    }
}
