//! NIST ACVP (<https://github.com/usnistgov/ACVP-Server>) known-answer tests.
//!
//! The `internalProjection.json` files of the test vector sets are vendored
//! under `vectors/nist-acvp/` (see `vectors/sources/` for where each one comes
//! from) and read at run time (`tests/vectors.rs`), so these tests always run.
//! The files of a set too large to vendor (SLH-DSA's) are listed in
//! `ci/acvp_vectors.toml`, with their SHA-256, and read from the directory `ci/fetch_acvp_vectors.py` downloads
//! them to, named by `ACVP_ROOT` ([`fetched`]); if it is not set, the tests
//! of those files are skipped (CI always sets it).

/// The environment variable naming the directory of the downloaded ACVP
/// files. A relative path is relative to the crate root.
pub const ROOT_VAR: &str = "ACVP_ROOT";

/// The text of the downloaded file `path` (as `ci/acvp_vectors.toml` names
/// it), or `None` if `ACVP_ROOT` is not set (the test is then skipped).
pub fn fetched(path: &str) -> Option<String> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(std::env::var_os(ROOT_VAR)?);
    let file = root.join(path);
    let text = std::fs::read_to_string(&file);
    Some(text.unwrap_or_else(|e| {
        panic!(
            "reading {}: {e} (see ci/fetch_acvp_vectors.py)",
            file.display()
        )
    }))
}

mod mldsa;
mod mldsa44;
mod mldsa65;
mod mldsa87;
mod mlkem;
mod mlkem1024;
mod mlkem768;
mod slhdsa;
mod slhdsa_shake_128f;
mod slhdsa_shake_128s;
mod slhdsa_shake_192f;
mod slhdsa_shake_192s;
mod slhdsa_shake_256f;
mod slhdsa_shake_256s;
