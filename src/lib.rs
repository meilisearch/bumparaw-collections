//! Collections backed by [`bumpalo`] and [`serde_json::value::RawValue`].
//!
//! That combination allows to manipulate shared references while doing minimal and gradual JSON parsing.

#![warn(missing_docs)]

/// Contains [`allocator_api2::alloc::Allocator`] implementations for [`bumpalo`] objects.
pub mod alloc;
/// Contains advanced type for [`bumpalo`]-enabled deserialization.
pub mod de;
/// Contains a simple `str` interner
pub mod interner;
/// Contains [`crate::map::RawMap`], [`crate::map::FrozenMap`] and associated types.
pub mod map;
/// Parses [`serde_json::value::RawValue`] in bumpalo-backed types.
mod value;
/// Contains [`crate::vec::RawVec`] and associated types.
pub mod vec;

pub use map::RawMap;
pub use value::Value;
pub use vec::RawVec;

#[cfg(test)]
mod test;
