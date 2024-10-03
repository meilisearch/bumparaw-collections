use bumpalo::Bump;
use hashbrown::HashSet;

/// A string interner based on [`HashSet`].
///
/// All allocations occur in the provided [`Bump`].
pub struct Interner<'bump> {
    set: HashSet<&'bump str, hashbrown::DefaultHashBuilder, &'bump Bump>,
}

impl<'bump> Interner<'bump> {
    /// Constructs a new interner backed by the specified allocator.
    pub fn new_in(bump: &'bump Bump) -> Self {
        Self {
            set: HashSet::new_in(bump),
        }
    }

    /// Returns the interned version of `s`, interning it if necessary.
    pub fn interned(&mut self, s: &str) -> &'bump str {
        let bump = *self.set.allocator();
        self.set.get_or_insert_with(s, |s| bump.alloc_str(s))
    }

    /// Get the interned version of `s` if it was already interned, otherwise `None`.
    pub fn get(&self, s: &str) -> Option<&'bump str> {
        self.set.get(s).copied()
    }

    /// A view of the underlying [`HashSet`].
    pub fn as_set(&self) -> &HashSet<&'bump str, hashbrown::DefaultHashBuilder, &'bump Bump> {
        &self.set
    }
}
