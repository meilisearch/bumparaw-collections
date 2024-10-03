//! Collections backed by [`bumpalo`] and [`serde_json::value::RawValue`].
//!
//! That combination allows to manipulate shared references while doing minimal and gradual JSON parsing.

#![warn(missing_docs)]

/// Contains advanced type for [`bumpalo`]-enabled deserialization.
pub mod de;
/// Contains a simple `str` interner
pub mod interner;
/// Contains [`crate::map::RawMap`] and associated types.
pub mod map;
/// Contains [`crate::vec::RawVec`] and associated types.
pub mod vec;

pub use map::RawMap;
pub use vec::RawVec;

#[cfg(test)]
mod test;
