//! The vendored test vector files, under `vectors/` (see
//! `vectors/sources/`), read when a test first asks for one.
//!
//! They were compiled into the test binary (`include_str!`): 31 MB of
//! constants that every build of the tests hashed, encoded and linked again,
//! a twentieth of the time the test binary took to build.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Mutex;

/// The text of the file `path`, relative to the crate root (`vectors/…`),
/// read once for every test that asks for it.
pub fn text(path: &'static str) -> &'static str {
    static FILES: Mutex<BTreeMap<&str, &str>> = Mutex::new(BTreeMap::new());
    let mut files = FILES.lock().unwrap();
    files.entry(path).or_insert_with(|| {
        let file = Path::new(env!("CARGO_MANIFEST_DIR")).join(path);
        let text = std::fs::read_to_string(&file);
        text.unwrap_or_else(|e| panic!("reading {}: {e}", file.display()))
            .leak()
    })
}
