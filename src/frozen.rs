/// A trait for objects that can be "frozen".
///
/// See module-level explanation for details.
///
/// # Safety
///
/// It is only safe to implement on types that are not referencing any thread local values as the type will be `Send` and can be used on different threads.
pub unsafe trait Freezable<'a> {
    /// Result of frozing the object.
    type Frozen: 'a + Send;

    /// Freezes the object
    fn freeze(&'a mut self) -> Self::Frozen;
}
