//! CAST5's modes of operation: pyca/cryptography's CAST5-CBC, CAST5-OFB and
//! CAST5-CFB64 vectors, vendored under `vectors/` (see `vectors/sources/`),
//! a block at a time, in pieces, and with a partial last segment.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

mod cast5_cbc;
mod cast5_cfb;
mod cast5_ofb;

/// A record's key, chaining value, plaintext and ciphertext.
type Record = (Vec<u8>, [u8; 8], Vec<u8>, Vec<u8>);

/// The records of a pyca/cryptography vector file.
fn records(text: &str) -> Vec<Record> {
    let unhex = |text: &str| -> Vec<u8> {
        (0..text.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
            .collect()
    };
    text.split("\n\n")
        .filter_map(|record| {
            let field = |name: &str| {
                record
                    .lines()
                    .find_map(|l| l.strip_prefix(name)?.trim().strip_prefix('='))
                    .map(|v| unhex(v.trim()))
            };
            Some((
                field("KEY")?,
                field("IV")?.try_into().unwrap(),
                field("PLAINTEXT")?,
                field("CIPHERTEXT")?,
            ))
        })
        .collect()
}
