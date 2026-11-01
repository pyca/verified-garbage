//! Parsing the text of the vendored vector files.

use std::collections::BTreeMap;

/// The `key = value` lines of `record`, trimmed, by key (a key given twice
/// keeps its last value). It inserts them one by one: collecting them into
/// the map compiled a sort for them.
pub fn fields(record: &str) -> BTreeMap<&str, &str> {
    let mut fields = BTreeMap::new();
    for line in record.lines() {
        if let Some((key, value)) = line.trim().split_once(" = ") {
            fields.insert(key, value);
        }
    }
    fields
}

/// The fields of one test vector of an RFC: `label: hex`, with continuation
/// lines `: hex`, labels in lower case with single spaces (RFC 3686 writes
/// both `Counter Block (1)` and `Counter block (1)`, RFC 5528
/// `Key Stream    (1)`). Lines whose value is not hex (the title,
/// `Plaintext String`) are not fields.
pub fn labelled(vector: &str) -> Vec<(String, Vec<u8>)> {
    let mut out: Vec<(String, String)> = Vec::new();
    for line in vector.lines() {
        let Some((label, value)) = line.split_once(':') else {
            continue;
        };
        let label = label
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
            .to_lowercase();
        if label.is_empty() {
            out.last_mut().unwrap().1.push_str(value);
        } else if value
            .chars()
            .all(|c| c.is_ascii_hexdigit() || c.is_whitespace())
        {
            out.push((label, value.to_string()));
        }
    }
    let mut fields = Vec::new();
    for (label, value) in out {
        fields.push((label, crate::bytes::unhex_spaced(&value)));
    }
    fields
}

/// The value of the field `label` of [`labelled`]'s `fields`.
pub fn get<'a>(fields: &'a [(String, Vec<u8>)], label: &str) -> &'a [u8] {
    &fields.iter().find(|(k, _)| k == label).unwrap().1
}
