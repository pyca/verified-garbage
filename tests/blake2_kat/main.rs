//! The known-answer tests of the BLAKE2 reference implementation
//! (`testvectors/blake2-kat.json` of <https://github.com/BLAKE2/BLAKE2>).
//!
//! The file is vendored under `vectors/blake2-kat/` (see
//! `vectors/sources/blake2-kat.toml` for where it comes from) and compiled
//! into the test binary, so these tests always run. Every BLAKE2b and BLAKE2s
//! vector is checked (the file's other functions, BLAKE2bp, BLAKE2sp, BLAKE2Xb
//! and BLAKE2Xs, are not implemented): the digests of inputs of 0 to 255
//! bytes, unkeyed and with a key of the largest size.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

mod blake2b;
mod blake2s;

use crate::bytes::unhex;
use crate::json_struct;

json_struct! {
    /// A vector of the file: the digest `out` of `input` with the key `key` (none
    /// if empty), all hex.
    struct Raw {
        hash: String,
        #[json(rename = "in")]
        input: String,
        key: String,
        out: String,
    }
}

/// A vector, decoded.
struct Vector {
    input: Vec<u8>,
    key: Vec<u8>,
    out: Vec<u8>,
}

/// The vectors of the function `hash` (`"blake2b"` or `"blake2s"`).
fn vectors(hash: &str) -> Vec<Vector> {
    let raw: Vec<Raw> = crate::json::parse(
        "blake2-kat.json",
        &crate::vectors::text("vectors/blake2-kat/blake2-kat.json"),
    );
    raw.into_iter()
        .filter(|v| v.hash == hash)
        .map(|v| Vector {
            input: unhex(&v.input),
            key: unhex(&v.key),
            out: unhex(&v.out),
        })
        .collect()
}
