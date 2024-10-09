use std::cell::RefCell;

use bumpalo::Bump;

use crate::RawMap;

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
    let bump_ref = crate::alloc::RefBump::new(bump.borrow());

    let hash = {
        let s = bump_ref.alloc_str("titi");
        let mut hash = hashbrown::HashMap::new_in(bump_ref.clone());
        hash.insert(s, 42);

        hash
    };

    assert!(bump.try_borrow_mut().is_err());

    drop(hash);
    drop(bump_ref);
    assert!(bump.try_borrow_mut().is_ok());
}
