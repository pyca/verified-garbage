//! Parsing the published FIPS 186-4 DSA response files, shared with unit tests.
extern crate alloc;
use alloc::{collections::BTreeMap, string::String, vec, vec::Vec};

pub fn vectors(text: &str, signing: bool) -> Vec<BTreeMap<String, String>> {
    let mut fields = BTreeMap::new();
    let mut cases = Vec::new();
    for line in text.lines().map(str::trim) {
        if line.starts_with("[mod = ") {
            fields.insert(
                "Hash".into(),
                line.rsplit(", ")
                    .next()
                    .unwrap()
                    .trim_end_matches(']')
                    .into(),
            );
        } else if let Some((key, value)) = line.split_once(" = ") {
            fields.insert(key.into(), value.into());
            if (signing && key == "S") || (!signing && key == "Result") {
                cases.push(fields.clone());
            }
        }
    }
    assert_eq!(cases.len(), 300);
    cases
}

pub fn hex(s: &str, width: usize) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2));
    let mut value: Vec<u8> = (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect();
    if value.len() < width {
        let mut padded = vec![0; width - value.len()];
        padded.append(&mut value);
        value = padded;
    }
    value
}
