//! SM4-CTR: the CTR examples (A.2.5) of the Internet-Draft
//! draft-ribose-cfrg-sm4-10, unmodified
//! under vectors/, whole, in pieces and truncated; and CTR from ECB
//! (`Sm4Ecb`, tested on the draft's ECB examples) on every length up to
//! a few groups of sixteen blocks and across the carries of the counter.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::sm4_ctr::Sm4Ctr;
use verified_garbage::sm4_ecb::Sm4Ecb;

use super::{field, section};

/// `ctr` plus `k`, modulo `2¹²⁸`.
fn add(mut ctr: [u8; 16], mut k: usize) -> [u8; 16] {
    for byte in ctr.iter_mut().rev() {
        let (sum, carry) = byte.overflowing_add(k as u8);
        *byte = sum;
        k = (k >> 8) + usize::from(carry);
    }
    ctr
}

/// CTR from ECB: `data` XORed with the encryptions of `ctr`, `ctr + 1`, ….
fn reference(key: &[u8; 16], ctr: [u8; 16], data: &[u8]) -> Vec<u8> {
    let start = u128::from_be_bytes(ctr);
    let mut keystream = crate::bytes::counter_blocks(start, data.len().div_ceil(16));
    Sm4Ecb::new(key).encrypt(&mut keystream).unwrap();
    crate::bytes::xor(data, &keystream)
}

/// `apply_keystream` on `data` from `ctr`, whole and split at every block
/// boundary, gives `expected` and leaves `ctr` plus the number of blocks.
fn check(ctx: &Sm4Ctr, ctr: [u8; 16], data: &[u8], expected: &[u8]) {
    let after = add(ctr, data.len().div_ceil(16));
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
        assert_eq!(c, add(ctr, offset / 16));
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
            assert_eq!(c, add(iv, len.div_ceil(16)));
        }
    }
}

/// Every length up to three groups of sixteen blocks and a bit, from
/// counter blocks that carry across each 32-bit word boundary or wrap entirely.
#[test]
fn from_ecb() {
    let key: [u8; 16] = crate::bytes::pattern_array(17, 3);
    let ctx = Sm4Ctr::new(&key);
    let data: Vec<u8> = crate::bytes::pattern(16 * 50 + 7, 31, 7);
    let low = u128::from(u64::MAX - 20);
    for ctr in [
        [0; 16],
        crate::bytes::pattern_array(11, 0),
        (u128::from(u32::MAX) - 20).to_be_bytes(),
        ((1u128 << 96) - 21).to_be_bytes(),
        low.to_be_bytes(),
        ((5 << 64) | low).to_be_bytes(),
        (u128::MAX - 20).to_be_bytes(),
    ] {
        for len in (0..=data.len()).step_by(5) {
            let input = &data[..len];
            let expected = reference(&key, ctr, input);
            let mut c = ctr;
            let mut output = input.to_vec();
            ctx.apply_keystream(&mut c, &mut output);
            assert_eq!(output, expected);
            assert_eq!(c, add(ctr, len.div_ceil(16)));
        }
        check(&ctx, ctr, &data, &reference(&key, ctr, &data));
    }
}

/// Unaligned slices and every tail through seventeen blocks;
/// bytes outside the requested slice must remain untouched.
#[test]
fn unaligned_batches() {
    let key = crate::bytes::pattern_array(7, 1);
    let ctx = Sm4Ctr::new(&key);
    let ctr = (u128::MAX - 8).to_be_bytes();
    for offset in 1..=4 {
        for len in 0..=16 * 17 {
            let mut buffer = vec![0xa5; offset + len + 4];
            let expected = reference(&key, ctr, &buffer[offset..offset + len]);
            let mut c = ctr;
            ctx.apply_keystream(&mut c, &mut buffer[offset..offset + len]);
            assert_eq!(&buffer[offset..offset + len], expected);
            assert_eq!(c, add(ctr, len.div_ceil(16)));
            assert!(crate::bytes::all_equal(&buffer[..offset], 0xa5));
            assert!(crate::bytes::all_equal(&buffer[offset + len..], 0xa5));
        }
    }
}
