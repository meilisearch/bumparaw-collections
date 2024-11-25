use std::alloc::Layout;
use std::cell::Cell;
use std::marker;
use std::mem::{self, needs_drop};
use std::ptr::{self, NonNull};

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
    head: Option<NonNull<Node>>,
    tail: Option<(NonNull<Node>, u32)>,
    // The number of times an initial value cannot be used as
    // it is larger than the smallest value of the block being
    // compressed.
    // skipped_initials: usize,
    _marker: marker::PhantomData<B>,
}

#[derive(Debug)]
#[repr(C)]
struct Node {
    // use interior mutability:
    // as the predecessor node has a link to this node by the time this node
    // is mutated to link to its successor node, it is no longer possible to
    // assert exclusivity of the reference to perform that mutation.
    next_node: Cell<Option<NonNull<u8>>>,
    next_node_len: Cell<u32>,
    num_bits: u8,
    mantissa: u8,
    bytes: [u8],
}

impl Node {
    const BASE_SIZE: usize = mem::size_of::<(Option<NonNull<u8>>, u32, u8, u8)>();

    #[allow(clippy::mut_from_ref)]
    fn new_in(block_size: usize, bump: &Bump) -> &mut Node {
        let total_size = Self::BASE_SIZE + block_size;
        let align = mem::align_of::<Option<NonNull<Node>>>();
        let layout = Layout::from_size_align(total_size, align).unwrap();
        let non_null = bump.alloc_layout(layout);

        unsafe {
            // Init everything to zero and the next pointer too!
            ptr::write_bytes(non_null.as_ptr(), 0, total_size);
            &mut *fatten(non_null, block_size)
        }
    }

    fn set_next_node(&self, node: &Node) {
        let len = node.bytes.len();
        self.next_node_len.set(len.try_into().unwrap());
        self.next_node
            .set(NonNull::new((node as *const Node) as *mut u8));
    }

    fn next_node(&self) -> Option<&Node> {
        self.next_node
            .get()
            .map(|data| unsafe { &*fatten(data, self.next_node_len.get() as usize) })
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
        // If the last inserted number is already this one, we just stop here
        if self.last == Some(n) {
            return;
        }

        self.last = Some(n);
        self.area[self.area_len] = n;
        self.area_len += 1;

        // If we don't need to push the area we just stop here
        if self.area_len != self.area.len() {
            return;
        }

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
                        initial_from_mantissa(initial, m).map_or(false, |n| n < self.area[0])
                    })
                    .map(|m| (Some(initial), m))
                    .unwrap_or((None, u8::MAX))
            }
            None => (None, u8::MAX),
        };

        let bp = B::new();
        let bits = bp.num_bits_strictly_sorted(initial, self.area);
        let block_size = B::compressed_block_size(bits);

        let next_tail = Node::new_in(block_size, self.bump);
        debug_assert_eq!(next_tail.bytes.len(), block_size);
        next_tail.num_bits = bits;
        next_tail.mantissa = mantissa;
        debug_assert!(next_tail.next_node().is_none());

        // self.skipped_initials += initial.is_none() as usize;

        let new_initial = self.area[0];
        let initial = initial.and_then(|i| initial_from_mantissa(i, mantissa));
        debug_assert!(initial.map_or(true, |n| n < self.area[0]));
        let size = bp.compress_strictly_sorted(initial, self.area, &mut next_tail.bytes, bits);
        debug_assert_eq!(next_tail.bytes.len(), size);

        match &mut self.tail {
            Some((tail, initial)) => {
                let previous_tail = unsafe { tail.as_ref() };
                *initial = new_initial;
                debug_assert!(previous_tail.next_node().is_none());
                *tail = next_tail.into();
                // **WARNING**: setting the reference to next tail must be done **after** `next_tail.into()`,
                //  because `next_tail.into()` is a `self` call on a `&mut`,
                //  invalidating any prior reference to `next_tail`
                previous_tail.set_next_node(next_tail);
            }
            None => {
                debug_assert!(self.head.is_none());
                let next_tail = next_tail.into();
                self.head = Some(next_tail);
                self.tail = Some((next_tail, new_initial));
            }
        }

        self.area_len = 0;
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
            head: self.0.head.take().map(|nn| unsafe { nn.as_ref() }),
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
            self.head = node.next_node();

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

/// Constructs a typed fat-pointer from a raw pointer and the allocation size.
unsafe fn fatten(data: NonNull<u8>, len: usize) -> *mut Node {
    ptr::slice_from_raw_parts_mut(data.as_ptr(), len) as *mut Node
}

/// Make sure that Node base size has a size of 16 bytes.
const _NODE_SIZE_16: () = if Node::BASE_SIZE != 16 {
    unreachable!()
};

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

        for n in 0..10_000 {
            bbbul.insert(n);
        }

        let mut frozen = FrozenBbbul::new(bbbul);
        let mut iter = frozen.iter_and_clear();
        let mut expected: HashSet<u32> = (0..10_000).collect();
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
        for n in (0..10_000).rev() {
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
        for _ in 0..10_000 {
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
