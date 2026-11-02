//! SM4-CTR: the CTR examples (A.2.5) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified under vectors/, whole, in pieces,
//! truncated, and in place in unaligned buffers.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::sm4_ctr::Sm4Ctr;

use super::{field, section};
use crate::bytes::counter_add;

/// `apply_keystream` on `data` from `ctr`, whole and split at every block
/// boundary, gives `expected` and leaves `ctr` plus the number of blocks.
fn check(ctx: &Sm4Ctr, ctr: [u8; 16], data: &[u8], expected: &[u8]) {
    let after = counter_add(&ctr, data.len().div_ceil(16));
    let mut c = ctr;
    let mut output = data.to_vec();
    ctx.apply_keystream(&mut c, &mut output);
    assert_eq!(output, expected);
    assert_eq!(c, after);
    for offset in (0..=data.len()).step_by(16) {
        let mut c = ctr;
        let mut output = data.to_vec();
        ctx.apply_keystream(&mut c, &mut []);
        assert_eq!(c, ctr);
        ctx.apply_keystream(&mut c, &mut output[..offset]);
        assert_eq!(c, counter_add(&ctr, offset / 16));
        ctx.apply_keystream(&mut c, &mut output[offset..]);
        assert_eq!(output, expected);
        assert_eq!(c, after);
    }
}

#[test]
fn draft_examples() {
    for (from, to) in [
        ("A.2.5.1.  Example 1", "A.2.5.2.  Example 2"),
        ("A.2.5.2.  Example 2", "Appendix B.  Sample Implementation"),
    ] {
        let text = &section(from, to);
        let key: [u8; 16] = field(text, "Encryption key:").try_into().unwrap();
        let iv: [u8; 16] = field(text, "IV:").try_into().unwrap();
        let plaintext = field(text, "Plaintext:");
        let ciphertext = field(text, "Ciphertext:");
        let ctx = Sm4Ctr::new(&key);
        check(&ctx, iv, &plaintext, &ciphertext);
        check(&ctx, iv, &ciphertext, &plaintext);
        // Every prefix, the last block partial.
        for len in 0..=plaintext.len() {
            let mut c = iv;
            let mut output = plaintext[..len].to_vec();
            ctx.apply_keystream(&mut c, &mut output);
            assert_eq!(output, ciphertext[..len]);
            assert_eq!(c, counter_add(&iv, len.div_ceil(16)));
        }
    }
}

/// The examples in place, at every offset of the data and the counter
/// block, leave the bytes around them unchanged.
#[test]
fn unaligned_buffers() {
    for (from, to) in [
        ("A.2.5.1.  Example 1", "A.2.5.2.  Example 2"),
        ("A.2.5.2.  Example 2", "Appendix B.  Sample Implementation"),
    ] {
        let text = &section(from, to);
        let key: [u8; 16] = field(text, "Encryption key:").try_into().unwrap();
        let iv: [u8; 16] = field(text, "IV:").try_into().unwrap();
        let plaintext = field(text, "Plaintext:");
        let ciphertext = field(text, "Ciphertext:");
        let ctx = Sm4Ctr::new(&key);
        let after = counter_add(&iv, plaintext.len().div_ceil(16));
        for io in [
            (&plaintext[..], &ciphertext[..]),
            (&ciphertext[..], &plaintext[..]),
        ] {
            crate::modes::check_unaligned(iv, io, after, &|c, b| ctx.apply_keystream(c, b));
        }
    }
}
