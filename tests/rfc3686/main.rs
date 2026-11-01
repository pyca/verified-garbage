//! The AES-CTR test vectors of RFC 3686 §6, read from the byte-for-byte
//! vendored RFC, and the increment of the counter block across its words and
//! past `2¹²⁸`, against AES-ECB on the counter blocks.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::bytes::counter_add;
use crate::text::{get, labelled};
use verified_garbage::aes_ctr::{AesCtr, InvalidKeyLength};
use verified_garbage::aes_ecb::AesEcb;

/// Checks a message in one call, split at every block boundary, one call per
/// block, and cut short at each length, with the counter block left after
/// each.
fn check(ctx: &AesCtr, ctr: &[u8; 16], input: &[u8], expected: &[u8]) {
    let blocks = input.len().div_ceil(16);
    let mut output = input.to_vec();
    let mut chain = *ctr;
    ctx.apply_keystream(&mut chain, &mut output);
    assert_eq!(output, expected);
    assert_eq!(chain, counter_add(ctr, blocks));
    for offset in (0..=input.len()).step_by(16) {
        let mut output = input.to_vec();
        let mut chain = *ctr;
        ctx.apply_keystream(&mut chain, &mut []);
        assert_eq!(chain, *ctr);
        ctx.apply_keystream(&mut chain, &mut output[..offset]);
        assert_eq!(chain, counter_add(ctr, offset / 16));
        ctx.apply_keystream(&mut chain, &mut output[offset..]);
        assert_eq!(output, expected);
        assert_eq!(chain, counter_add(ctr, blocks));
    }
    let mut output = input.to_vec();
    let mut chain = *ctr;
    for block in output.chunks_mut(16) {
        ctx.apply_keystream(&mut chain, block);
    }
    assert_eq!(output, expected);
    assert_eq!(chain, counter_add(ctr, blocks));
    for len in 0..input.len() {
        let mut output = input[..len].to_vec();
        let mut chain = *ctr;
        ctx.apply_keystream(&mut chain, &mut output);
        assert_eq!(output, expected[..len]);
        assert_eq!(chain, counter_add(ctr, len.div_ceil(16)));
    }
}

#[test]
fn rfc3686_test_vectors() {
    // The section itself, not its line in the table of contents.
    let text = crate::vectors::text("vectors/rfc3686/rfc3686.txt");
    let section = text.rsplit_once("6.  Test Vectors").unwrap().1;
    let section = section.split_once("7.  Security Considerations").unwrap().0;
    let mut key_lens = Vec::new();
    for vector in section.split("Test Vector #").skip(1) {
        let fields = labelled(vector);
        let key = get(&fields, "aes key");
        let ctr: [u8; 16] = get(&fields, "counter block (1)").try_into().unwrap();
        let plaintext = get(&fields, "plaintext");
        let ciphertext = get(&fields, "ciphertext");
        key_lens.push(key.len());
        let ctx = AesCtr::new(key).unwrap();
        check(&ctx, &ctr, plaintext, ciphertext);
        check(&ctx, &ctr, ciphertext, plaintext);
        // The key stream is CTR of zeros, block by block from its counter block.
        let blocks = plaintext.len().div_ceil(16);
        let mut stream = vec![0; 16 * blocks];
        let mut chain = ctr;
        ctx.apply_keystream(&mut chain, &mut stream);
        for (j, block) in stream.chunks(16).enumerate() {
            assert_eq!(
                get(&fields, &format!("counter block ({})", j + 1)),
                counter_add(&ctr, j)
            );
            assert_eq!(get(&fields, &format!("key stream ({})", j + 1)), block);
        }
    }
    assert_eq!(key_lens, [16, 16, 16, 24, 24, 24, 32, 32, 32]);
}

/// The counter block's increment carries across its 32- and 64-bit words and
/// wraps from `1¹²⁸` to `0¹²⁸`: the output blocks are AES (by AES-ECB) of
/// the counter blocks counted with `u128`.
#[test]
fn counter_carries_and_wraps() {
    let starts: [u128; 6] = [
        u128::MAX - 2,
        u128::MAX,
        (1 << 32) - 2,
        (1 << 64) - 3,
        (1 << 96) - 1,
        0x0123_4567_89ab_cdef_ffff_ffff_ffff_fffe,
    ];
    for key_len in [16, 24, 32] {
        let key: Vec<_> = crate::bytes::pattern(key_len, 29, 7);
        let ctx = AesCtr::new(&key).unwrap();
        let ecb = AesEcb::new(&key).unwrap();
        for start in starts {
            let ctr = start.to_be_bytes();
            let message: Vec<_> = crate::bytes::pattern(16 * 5 + 7, 11, 5);
            let mut stream = crate::bytes::counter_blocks(start, message.len().div_ceil(16));
            ecb.encrypt(&mut stream).unwrap();
            let expected: Vec<_> = crate::bytes::xor(&message, &stream);
            check(&ctx, &ctr, &message, &expected);
        }
    }
}

#[test]
fn limits_and_lengths() {
    for len in 0..=40 {
        let key: Vec<_> = crate::bytes::pattern(len, 17, 3);
        if !matches!(len, 16 | 24 | 32) {
            assert!(matches!(AesCtr::new(&key), Err(InvalidKeyLength)));
            continue;
        }
        let ctx = AesCtr::new(&key).unwrap();
        let mut ctr = [0x3c; 16];
        ctx.apply_keystream(&mut ctr, &mut []);
        assert_eq!(ctr, [0x3c; 16]);
    }
}
