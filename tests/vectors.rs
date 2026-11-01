//! The vendored test vector files, under `vectors/` (see
//! `vectors/sources/`), read when a test asks for one.
//!
//! They were compiled into the test binary (`include_str!`): 31 MB of
//! constants that every build of the tests hashed, encoded and linked again,
//! a twentieth of the time the test binary took to build.

use std::path::Path;

/// The text of the file `path`, relative to the crate root (`vectors/…`),
/// leaked so that it lives as long as `include_str!`'s did and tests can
/// keep borrowing from it: a run reads 105 files, 263 times in all.
pub fn text(path: &str) -> &'static str {
    let file = Path::new(env!("CARGO_MANIFEST_DIR")).join(path);
    let text = std::fs::read_to_string(&file);
    text.unwrap_or_else(|e| panic!("reading {}: {e}", file.display()))
        .leak()
}
