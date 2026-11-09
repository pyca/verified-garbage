//! SM4-OFB: the OFB examples (A.2.3) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, truncated and split
//! (`tests/modes.rs`), and in place in unaligned buffers.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cipher::sm4::Sm4Ofb;

use super::{field, section};

/// An example: key, IV, plaintext and ciphertext.
type Example = ([u8; 16], [u8; 16], Vec<u8>, Vec<u8>);

/// The examples.
fn examples() -> Vec<Example> {
    let mut examples = Vec::new();
    for (from, to) in [
        ("A.2.3.1.  Example 1", "A.2.3.2.  Example 2"),
        ("A.2.3.2.  Example 2", "A.2.4.  SM4-CFB Examples"),
    ] {
        let text = &section(from, to);
        examples.push((
            field(text, "Encryption Key:").try_into().unwrap(),
            field(text, "IV:").try_into().unwrap(),
            field(text, "Plaintext:"),
            field(text, "Ciphertext:"),
        ));
    }
    examples
}

#[test]
fn draft_examples() {
    for (key, iv, plaintext, ciphertext) in examples() {
        let vector = (&plaintext[..], &ciphertext[..]);
        for io in [vector, (&ciphertext[..], &plaintext[..])] {
            crate::modes::check(
                iv,
                io,
                &|iv| Sm4Ofb::new(&key, iv),
                Sm4Ofb::apply_keystream,
                Sm4Ofb::apply_keystream_final,
            );
        }
    }
}

/// The examples in place, at every offset of the data, leave the bytes
/// around them unchanged.
#[test]
fn unaligned_buffers() {
    for (key, iv, plaintext, ciphertext) in examples() {
        for io in [
            (&plaintext[..], &ciphertext[..]),
            (&ciphertext[..], &plaintext[..]),
        ] {
            crate::modes::check_unaligned(
                iv,
                io,
                &|iv| Sm4Ofb::new(&key, iv),
                Sm4Ofb::apply_keystream_final,
            );
        }
    }
}
