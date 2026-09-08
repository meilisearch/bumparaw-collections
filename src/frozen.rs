/// A trait for objects that can be "frozen".
///
/// See module-level explanation for details.
///
/// # Safety
///
/// TBD
pub unsafe trait Freezable<'a> {
    /// Result of frozing the object.
    type Frozen: 'a + Send;

    /// Freezes the object
    fn freeze(&'a mut self) -> Self::Frozen;
}
