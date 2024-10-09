use std::{
    cell::Ref,
    ops::{Deref, DerefMut},
};

use allocator_api2::alloc::Allocator;
use bumpalo::Bump;

/// A newtype wrapper to implement [`Allocator`] on `Ref<Bump>`.
pub struct RefBump<'bump>(Ref<'bump, Bump>);

impl<'bump> RefBump<'bump> {
    /// Wraps a `Ref<Bump>` into a type that implements the [`Allocator`] trait.
    pub fn new(r: Ref<'bump, Bump>) -> Self {
        Self(r)
    }

    /// Clones the wrapped `Ref<Bump>`.
    ///
    /// See [`Ref::clone`] for more information.
    #[allow(clippy::should_implement_trait)] // really, go see [`Ref::clone`]
    pub fn clone(orig: &RefBump<'bump>) -> RefBump<'bump> {
        Self(Ref::clone(&orig.0))
    }

    /// Makes a new [`Ref`] for a component of the borrowed data.
    ///
    /// See [`Ref::map`] for more information.
    pub fn map<T, F>(orig: RefBump<'bump>, f: F) -> Ref<'bump, T>
    where
        F: FnOnce(&Bump) -> &T,
        T: ?Sized,
    {
        Ref::map(orig.0, f)
    }

    /// Makes a new [`Ref`] for an optional component of the borrowed data.
    /// The original guard is returned as an `Err(..)` if the closure returns None.
    ///
    /// See [`Ref::filter_map`] for more information.
    pub fn filter_map<T, F>(orig: RefBump<'bump>, f: F) -> Result<Ref<'bump, T>, RefBump<'bump>>
    where
        F: FnOnce(&Bump) -> Option<&T>,
        T: ?Sized,
    {
        Ref::filter_map(orig.0, f).map_err(RefBump)
    }

    /// Splits a Ref into multiple Refs for different components of the borrowed data.
    ///
    /// See [`Ref::filter_map`] for more information.
    pub fn map_split<T, U, F>(orig: RefBump<'bump>, f: F) -> (Ref<'bump, T>, Ref<'bump, U>)
    where
        F: FnOnce(&Bump) -> (&T, &U),
        T: ?Sized,
        U: ?Sized,
    {
        Ref::map_split(orig.0, f)
    }
}

impl<'bump> Deref for RefBump<'bump> {
    type Target = Ref<'bump, Bump>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'bump> DerefMut for RefBump<'bump> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

unsafe impl<'bump> Allocator for RefBump<'bump> {
    #[inline]
    fn allocate(
        &self,
        layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, allocator_api2::alloc::AllocError> {
        self.0.deref().allocate(layout)
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        self.0.deref().deallocate(ptr, layout)
    }

    #[inline]
    fn allocate_zeroed(
        &self,
        layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, allocator_api2::alloc::AllocError> {
        self.0.deref().allocate_zeroed(layout)
    }

    #[inline]
    unsafe fn grow(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: std::alloc::Layout,
        new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, allocator_api2::alloc::AllocError> {
        self.0.deref().grow(ptr, old_layout, new_layout)
    }

    #[inline]
    unsafe fn grow_zeroed(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: std::alloc::Layout,
        new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, allocator_api2::alloc::AllocError> {
        self.0.deref().grow_zeroed(ptr, old_layout, new_layout)
    }

    #[inline]
    unsafe fn shrink(
        &self,
        ptr: std::ptr::NonNull<u8>,
        old_layout: std::alloc::Layout,
        new_layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, allocator_api2::alloc::AllocError> {
        self.0.deref().shrink(ptr, old_layout, new_layout)
    }

    #[inline]
    fn by_ref(&self) -> &Self
    where
        Self: Sized,
    {
        self
    }
}
