//! Collections backed by [`bumpalo`] and [`serde_json::value::RawValue`].
//!
//! That combination allows to manipulate shared references while doing minimal and gradual JSON parsing.

#![warn(missing_docs)]

/// Contains [`allocator_api2::alloc::Allocator`] implementations for [`bumpalo`] objects.
pub mod alloc;
/// Contains [`crate::bbbul::Bbbul`] and [`crate::bbbul::FrozenBbbul`] types.
pub mod bbbul;
/// Contains advanced type for [`bumpalo`]-enabled deserialization.
pub mod de;
/// Contains a trait related to the ability to "freeze" an object.
///
/// A frozen object is no longer mutable, but instead gains the ability to become [`Send`].
/// This is useful for objects containing referencing to a [`bumpalo::Bump`], because [`bumpalo::Bump`] is not [`Sync`].
pub mod frozen;
/// Contains a simple `str` interner
pub mod interner;
/// Contains [`crate::map::RawMap`], [`crate::map::FrozenMap`] and associated types.
pub mod map;
/// Parses [`serde_json::value::RawValue`] in bumpalo-backed types.
pub mod value;
/// Contains [`crate::vec::RawVec`] and associated types.
pub mod vec;

pub use bbbul::{Bbbul, FrozenBbbul};
pub use map::RawMap;
pub use value::Value;
pub use vec::RawVec;

#[cfg(test)]
mod test;
