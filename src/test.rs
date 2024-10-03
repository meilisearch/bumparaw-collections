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
