use std::{
    cell::{Ref, RefCell},
    ops::Deref as _,
};

use bumpalo::Bump;

use crate::{alloc::RefBump, RawMap};

#[test]
fn it_works() {
    let s = "{\"toto\":\"titi\"}";
    let raw = serde_json::from_str(s).unwrap();
    let bump = Bump::new();
    let top = RawMap::from_raw_value(raw, &bump).unwrap();

    assert_eq!(serde_json::to_string(&top).unwrap(), s);
}

#[test]
fn with_alloc() {
    let s = r#"{"contains a raw \"":"titi"}"#;
    let raw = serde_json::from_str(s).unwrap();
    let bump = Bump::new();
    let top = RawMap::from_raw_value(raw, &bump).unwrap();

    assert_eq!(serde_json::to_string(&top).unwrap(), s);
}

#[test]
fn test_ref_allocator() {
    let bump = RefCell::new(Bump::new());
    let bump_ref = RefBump::new(bump.borrow());

    let hash = {
        let s = bump_ref.alloc_str("titi");
        let mut hash = hashbrown::HashMap::new_in(RefBump::clone(&bump_ref));
        hash.insert(s, 42);

        hash
    };

    assert!(bump.try_borrow_mut().is_err());

    drop(hash);
    drop(bump_ref);
    assert!(bump.try_borrow_mut().is_ok());
}

#[test]
fn test_ref_map() {
    struct RefStr<'bump>(pub Ref<'bump, str>);

    impl std::hash::Hash for RefStr<'_> {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.0.hash(state);
        }
    }

    impl PartialEq for RefStr<'_> {
        fn eq(&self, other: &Self) -> bool {
            self.0.deref() == other.0.deref()
        }
    }

    impl Eq for RefStr<'_> {}

    let bump = RefCell::new(Bump::new());
    let bump_ref = RefBump::new(bump.borrow());

    let hash = {
        let mut hash = hashbrown::HashMap::new_in(bump_ref);
        let bump_ref_clone = RefBump::clone(hash.allocator());
        let s = RefStr(RefBump::map(bump_ref_clone, |bump| bump.alloc_str("toto")));

        hash.insert(s, 42);

        hash
    };

    assert!(bump.try_borrow_mut().is_err());

    drop(hash);

    assert!(bump.try_borrow_mut().is_ok());
}
