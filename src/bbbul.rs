use std::alloc::Layout;
use std::mem::{self, needs_drop};
use std::ptr::{self, NonNull};
use std::{marker, slice};

use bumpalo::Bump;

pub use bitpacking::{BitPacker, BitPacker1x, BitPacker4x, BitPacker8x};

/// A `Bbbul` is a list of arbitrary `u32`s that can be only read once
/// it as been frozzen by casting or wrapping it into a [`FrozenBbbul`].
///
/// ```
/// use std::collections::HashSet;
/// use raw_collections::{FrozenBbbul, Bbbul};
/// use bitpacking::BitPacker4x;
///
/// let bump = bumpalo::Bump::new();
/// let mut bbbul = Bbbul::<BitPacker4x>::new_in(&bump);
///
/// for n in 0..10000 {
///     bbbul.insert(n);
/// }
///
/// let mut frozen = FrozenBbbul::new(bbbul);
/// let mut iter = frozen.iter_and_clear();
/// let mut expected: HashSet<u32> = (0..10000).collect();
/// while let Some(block) = iter.next_block() {
///     block.iter().for_each(|n| assert!(expected.remove(n)));
/// }
/// assert!(expected.is_empty());
/// ```
#[derive(Debug)]
pub struct Bbbul<'bump, B> {
    bump: &'bump Bump,
    last: Option<u32>,
    area_len: usize,
    area: &'bump mut [u32],
    /// We must not have multiple references to the same memory
    /// when one of them is mutable. When reading the list from
    /// the head we make sure to first drop the &mut Nodes below.
    head: Option<NonNull<Node>>,
    /// Here we only keep &mut Node once. We made sure above to
    /// only have a pointer to the head and the next nodes.
    tail: Option<(&'bump mut Node, u32)>,
    // The number of times an initial value cannot be used as
    // it is larger than the smallest value of the block being
    // compressed.
    // skipped_initials: usize,
    _marker: marker::PhantomData<B>,
}

#[derive(Debug)]
#[repr(C)]
struct Node {
    next: Option<NonNull<Node>>,
    num_bits: u8,
    mantissa: u8,
    bytes: [u8],
}

impl Node {
    const BASE_SIZE: usize = mem::size_of::<(Option<NonNull<Node>>, u8)>();

    #[allow(clippy::mut_from_ref)]
    fn new_in(block_size: usize, bump: &Bump) -> &mut Node {
        let total_size = Self::BASE_SIZE + block_size;
        let align = mem::align_of::<Option<NonNull<Node>>>();
        let layout = Layout::from_size_align(total_size, align).unwrap();
        let non_null = bump.alloc_layout(layout);

        /// Constructs a typed fat-pointer from a raw pointer and the allocation size.
        // https://users.rust-lang.org/t/construct-fat-pointer-to-struct/29198/9
        unsafe fn fatten(data: NonNull<u8>, len: usize) -> *mut Node {
            let slice = unsafe { slice::from_raw_parts(data.as_ptr() as *mut (), len) };
            slice as *const [()] as *mut Node
        }

        unsafe {
            // Init everything to zero and the next pointer too!
            ptr::write_bytes(non_null.as_ptr(), 0, total_size);
            &mut *fatten(non_null, block_size)
        }
    }
}

impl<'bump, B: BitPacker> Bbbul<'bump, B> {
    /// Construct a new `Bbbul` type.
    pub fn new_in(bump: &'bump Bump) -> Bbbul<'bump, B> {
        Bbbul {
            bump,
            last: None,
            area_len: 0,
            area: bump.alloc_slice_fill_copy(B::BLOCK_LEN, 0),
            head: None,
            tail: None,
            // skipped_initials: 0,
            _marker: marker::PhantomData,
        }
    }

    /// Insert an arbitrary `u32` into this list and will compact
    /// them if needed.
    ///
    /// It is much more efficient in terms of compression to insert
    /// the numbers in sorted order.
    ///
    /// # Panics
    ///
    ///  - If the inserted `u32` as already been inserted previously.
    pub fn insert(&mut self, n: u32) {
        if self.last != Some(n) {
            self.last = Some(n);
            self.area[self.area_len] = n;
            self.area_len += 1;

            if self.area_len == self.area.len() {
                self.area.sort_unstable();

                // Checking in debug that the working area
                // does not contain duplicated integers.
                debug_assert!({
                    let mut vec = self.area.to_vec();
                    vec.dedup();
                    vec.len() == self.area.len()
                });

                let (initial, mantissa) = match self.tail {
                    Some((_, initial)) => {
                        (0..u8::BITS as u8) // shift from 0 to 31
                            .find(|&m| {
                                initial_from_mantissa(initial, m)
                                    .map_or(false, |n| n < self.area[0])
                            })
                            .map(|m| (Some(initial), m))
                            .unwrap_or((None, u8::MAX))
                    }
                    None => (None, u8::MAX),
                };

                let bp = B::new();
                let bits = bp.num_bits_strictly_sorted(initial, self.area);
                let block_size = B::compressed_block_size(bits);

                let node = Node::new_in(block_size, self.bump);
                debug_assert_eq!(node.bytes.len(), block_size);
                node.num_bits = bits;
                node.mantissa = mantissa;
                debug_assert!(node.next.is_none());

                // self.skipped_initials += initial.is_none() as usize;

                let new_initial = self.area[0];
                let initial = initial.and_then(|i| initial_from_mantissa(i, mantissa));
                debug_assert!(initial.map_or(true, |n| n < self.area[0]));
                let size = bp.compress_strictly_sorted(initial, self.area, &mut node.bytes, bits);
                debug_assert_eq!(node.bytes.len(), size);

                match &mut self.tail {
                    Some((tail, initial)) => {
                        *initial = new_initial;
                        debug_assert!(tail.next.is_none());
                        tail.next = NonNull::new(node);
                        *tail = node;
                    }
                    None => {
                        debug_assert!(self.head.is_none());
                        self.head = NonNull::new(node);
                        self.tail = Some((node, new_initial));
                    }
                }

                self.area_len = 0;
            }
        }
    }
}

/// A frozen version of the [`Bbbul`] type.
///
/// It is safe to cast the `Bbbul` type into this struct as it is just a transparant
/// wrapper struct.
#[repr(transparent)]
pub struct FrozenBbbul<'bump, B>(Bbbul<'bump, B>);

impl<'bump, B> FrozenBbbul<'bump, B> {
    /// Creates a `FrozenBbbul` that is `Send` and will never drop, allocate nor deallocate anything.
    pub fn new(mut bbbul: Bbbul<'bump, B>) -> FrozenBbbul<'bump, B> {
        // We must make sure we do not read nodes while we have still
        // have a mutable reference on one of them. So, we remove the
        // &mut Node in the tail and only keep the head NonNull<Node>.
        bbbul.tail = None;
        // eprintln!("skipped {}", bbbul.skipped_initials);
        FrozenBbbul(bbbul)
    }

    /// Removes all the numbers stored in this `Bbbul`.
    pub fn clear(&mut self) {
        self.0.area_len = 0;
        self.0.head = None;
        self.0.tail = None;
    }

    /// Returns wether this `Bbbul` is empty.
    pub fn is_empty(&self) -> bool {
        self.0.area_len == 0 && self.0.head.is_some()
    }

    /// Gives an iterator of block of integers and clears the `Bbbul` at the same time.
    pub fn iter_and_clear(&mut self) -> IterAndClear<'_, B> {
        IterAndClear {
            area_len: mem::replace(&mut self.0.area_len, 0),
            area: self.0.area,
            initial: None,
            head: self.0.head.take().map(|nn| unsafe { &*nn.as_ptr() }),
            _marker: marker::PhantomData,
        }
    }
}

/// # Safety
///
/// - The FrozenBbbul never reallocates.
/// - The FrozenBbbul does not leak a shared reference to the allocator.
///
/// So, it is safe to send the contained shared reference to the allocator
unsafe impl<'bump, B> Send for FrozenBbbul<'bump, B> {}

/// An non-standard iterator over the `u32`s in the [`FrozenBbbul`] type.
///
/// Returns the `u32`s in arbitrary order.
pub struct IterAndClear<'bump, B> {
    area_len: usize,
    area: &'bump mut [u32],
    initial: Option<u32>,
    head: Option<&'bump Node>,
    _marker: marker::PhantomData<B>,
}

impl<B: BitPacker> IterAndClear<'_, B> {
    /// The next block of `u32`s decompressed and ordered.
    ///
    /// Note that each block contains an ordered list of
    /// numbers but the number are not ordered between two blocks.
    pub fn next_block(&mut self) -> Option<&[u32]> {
        if self.area_len != 0 {
            let numbers = &mut self.area[..self.area_len];
            numbers.sort_unstable();
            self.area_len = 0;
            Some(numbers)
        } else if let Some(node) = self.head.take() {
            self.head = node.next.map(|nn| unsafe { &*nn.as_ptr() });

            let bp = B::new();
            let mantissa = node.mantissa;
            let initial = self
                .initial
                .and_then(|i| initial_from_mantissa(i, mantissa));
            let read_bytes =
                bp.decompress_strictly_sorted(initial, &node.bytes, self.area, node.num_bits);
            debug_assert_eq!(read_bytes, node.bytes.len());
            self.initial = Some(self.area[0]);

            Some(self.area)
        } else {
            None
        }
    }
}

fn initial_from_mantissa(initial: u32, mantissa: u8) -> Option<u32> {
    1u32.checked_shl(mantissa as u32).map(|d| initial / d)
}

/// Make sure that Bbbul does not need drop.
const _BBBUL_NEEDS_DROP: () = if needs_drop::<Bbbul<bitpacking::BitPacker4x>>() {
    unreachable!()
};

/// Make sure that FrozenBbbul does not need drop.
const _FROZEN_BBBUL_NEEDS_DROP: () = if needs_drop::<FrozenBbbul<bitpacking::BitPacker4x>>() {
    unreachable!()
};

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use bitpacking::{BitPacker1x, BitPacker4x};
    use rand::{RngCore, SeedableRng};

    use super::*;

    #[test]
    fn basic() {
        let bump = bumpalo::Bump::new();
        let mut bbbul = Bbbul::<BitPacker4x>::new_in(&bump);

        for n in 0..10000 {
            bbbul.insert(n);
        }

        let mut frozen = FrozenBbbul::new(bbbul);
        let mut iter = frozen.iter_and_clear();
        let mut expected: HashSet<u32> = (0..10000).collect();
        while let Some(block) = iter.next_block() {
            block.iter().for_each(|n| assert!(expected.remove(n)));
        }
        assert!(expected.is_empty());
    }

    #[test]
    fn basic_reverse() {
        let bump = bumpalo::Bump::new();
        let mut bbbul = Bbbul::<BitPacker1x>::new_in(&bump);

        let mut expected = HashSet::new();
        for n in (0..10000).rev() {
            expected.insert(n);
            bbbul.insert(n);
        }

        let mut frozen = FrozenBbbul::new(bbbul);
        let mut iter = frozen.iter_and_clear();
        while let Some(block) = iter.next_block() {
            block.iter().for_each(|n| assert!(expected.remove(n)));
        }
        assert!(expected.is_empty());
    }

    #[test]
    fn basic_with_rand() {
        let bump = bumpalo::Bump::new();
        let mut bbbul = Bbbul::<BitPacker4x>::new_in(&bump);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);

        let mut expected = HashSet::new();
        for _ in 0..100000 {
            let n = rng.next_u32();
            // Note that it is forbidden to insert the
            // same number multiple times.
            if expected.insert(n) {
                bbbul.insert(n);
            }
        }

        let mut frozen = FrozenBbbul::new(bbbul);
        let mut iter = frozen.iter_and_clear();
        while let Some(block) = iter.next_block() {
            block
                .iter()
                .for_each(|n| assert!(expected.remove(n), "removing {n}"));
        }
        assert!(expected.is_empty());
    }

    #[test]
    fn broken_initial() {
        let bump = bumpalo::Bump::new();
        let mut bbbul = Bbbul::<BitPacker4x>::new_in(&bump);

        let mut expected = HashSet::new();
        for n in (640..768).chain(0..128).chain(300..600) {
            expected.insert(n);
            bbbul.insert(n);
        }

        let mut frozen = FrozenBbbul::new(bbbul);
        let mut iter = frozen.iter_and_clear();
        while let Some(block) = iter.next_block() {
            block.iter().for_each(|n| {
                if *n == 641 {
                    eprintln!("trying to remove {n}")
                }
                assert!(expected.remove(n), "removing {n}")
            });
        }
        assert!(expected.is_empty());
    }
}
