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
