//! SM4-CFB128: the CFB examples (A.2.4) of the Internet-Draft
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

use verified_garbage::sm4_cfb::Sm4Cfb128;

use super::{field, section};

/// An example: key, IV, plaintext and ciphertext.
type Example = ([u8; 16], [u8; 16], Vec<u8>, Vec<u8>);

/// The examples.
fn examples() -> Vec<Example> {
    let mut examples = Vec::new();
    for (from, to) in [
        ("A.2.4.1.  Example 1", "A.2.4.2.  Example 2"),
        ("A.2.4.2.  Example 2", "A.2.5.  SM4-CTR Examples"),
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
        let ctx = Sm4Cfb128::new(&key);
        let vector = (&plaintext[..], &ciphertext[..]);
        let cfb = crate::modes::Feedback::Ciphertext;
        crate::modes::check(cfb, iv, vector, vector, &|iv, b| ctx.encrypt(iv, b));
        crate::modes::check(cfb, iv, vector, (&ciphertext, &plaintext), &|iv, b| {
            ctx.decrypt(iv, b)
        });
    }
}

/// The examples in place, at every offset of the data and the chaining
/// value, leave the bytes around them unchanged.
#[test]
fn feedback_buffers_unaligned() {
    for (key, iv, plaintext, ciphertext) in examples() {
        let ctx = Sm4Cfb128::new(&key);
        let after = ciphertext[ciphertext.len() - 16..].try_into().unwrap();
        crate::modes::check_unaligned(iv, (&plaintext, &ciphertext), after, &|iv, b| {
            ctx.encrypt(iv, b)
        });
        crate::modes::check_unaligned(iv, (&ciphertext, &plaintext), after, &|iv, b| {
            ctx.decrypt(iv, b)
        });
    }
}
