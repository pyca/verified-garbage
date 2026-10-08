//! NIST CAVP AES-CFB128 known-answer (KAT) and multi-block message (MMT)
//! vectors, with unmodified sources under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use std::collections::BTreeMap;

use verified_garbage::aes_cfb::{AesCfb128, InvalidKeyLength};

use super::unhex;

/// `AesCfb128::encrypt` or `AesCfb128::decrypt`.
type Direction = fn(&AesCfb128, &mut [u8; 16], &mut [u8]);

/// `CIPH_K` of the block before the `n`-th: the `n`-th plaintext block XOR
/// the `n`-th ciphertext block.
fn keystream_block(plaintext: &[u8], ciphertext: &[u8], n: usize) -> [u8; 16] {
    let mut o = [0; 16];
    for i in 0..16 {
        o[i] = plaintext[16 * (n - 1) + i] ^ ciphertext[16 * (n - 1) + i];
    }
    o
}

/// Checks a vector in both directions, in one call; with `split`, also in
/// two calls split at each block boundary, one call per block, and with the
/// message cut short at each length in its last block (a partial last
/// segment).
fn check(key: &[u8], iv: &[u8], plaintext: &[u8], ciphertext: &[u8], split: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    assert_eq!(plaintext.len() % 16, 0);
    let ctx = AesCfb128::new(key).unwrap();
    let iv: [u8; 16] = iv.try_into().unwrap();
    let n = plaintext.len() / 16;
    // The block to continue from after the message (no vector is empty),
    // and after a partial last segment.
    let last: [u8; 16] = ciphertext[ciphertext.len() - 16..].try_into().unwrap();
    let partial = keystream_block(plaintext, ciphertext, n);
    let directions: [(Direction, &[u8], &[u8]); 2] = [
        (AesCfb128::encrypt, plaintext, ciphertext),
        (AesCfb128::decrypt, ciphertext, plaintext),
    ];
    for (f, input, expected) in directions {
        let mut output = input.to_vec();
        let mut chain = iv;
        f(&ctx, &mut chain, &mut output);
        assert_eq!(output, expected);
        assert_eq!(chain, last);
        if split {
            for offset in (0..=input.len()).step_by(16) {
                let mut output = input.to_vec();
                let mut chain = iv;
                f(&ctx, &mut chain, &mut []);
                assert_eq!(chain, iv);
                f(&ctx, &mut chain, &mut output[..offset]);
                f(&ctx, &mut chain, &mut output[offset..]);
                assert_eq!(output, expected);
                assert_eq!(chain, last);
            }
            let mut output = input.to_vec();
            let mut chain = iv;
            for block in output.chunks_mut(16) {
                f(&ctx, &mut chain, block);
            }
            assert_eq!(output, expected);
            assert_eq!(chain, last);
            for len in input.len() - 15..input.len() {
                let mut output = input[..len].to_vec();
                let mut chain = iv;
                f(&ctx, &mut chain, &mut output);
                assert_eq!(output, expected[..len]);
                assert_eq!(chain, partial);
            }
        }
    }
}

/// Checks every vector of a response file, and returns how many there were.
fn check_file(text: &str, split: bool) -> usize {
    let mut count = 0;
    for record in text.replace('\r', "").split("\n\n") {
        let fields: BTreeMap<_, _> = record
            .lines()
            .filter_map(|line| line.trim().split_once(" = "))
            .collect();
        if !fields.contains_key("COUNT") {
            continue;
        }
        check(
            &unhex(fields["KEY"]),
            &unhex(fields["IV"]),
            &unhex(fields["PLAINTEXT"]),
            &unhex(fields["CIPHERTEXT"]),
            split,
        );
        count += 1;
    }
    count
}

#[test]
fn nist_cfb128() {
    let files = [
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128GFSbox128.rsp"),
            14,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128GFSbox192.rsp"),
            12,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128GFSbox256.rsp"),
            10,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128KeySbox128.rsp"),
            42,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128KeySbox192.rsp"),
            48,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128KeySbox256.rsp"),
            32,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128VarKey128.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128VarKey192.rsp"),
            384,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128VarKey256.rsp"),
            512,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128VarTxt128.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128VarTxt192.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb128/CFB128VarTxt256.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/CFB128MMT128.rsp"),
            20,
            true,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/CFB128MMT192.rsp"),
            20,
            true,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/CFB128MMT256.rsp"),
            20,
            true,
        ),
    ];
    let mut total = 0;
    for (text, expected, split) in files {
        let count = check_file(text, split);
        assert_eq!(count, expected);
        total += count;
    }
    assert_eq!(total, 2138);
}

#[test]
fn limits_and_lengths() {
    for len in 0..=40 {
        let key: Vec<_> = (0..len).map(|i| (17 * i + 3) as u8).collect();
        if !matches!(len, 16 | 24 | 32) {
            assert!(matches!(AesCfb128::new(&key), Err(InvalidKeyLength)));
            continue;
        }
        let ctx = AesCfb128::new(&key).unwrap();
        let mut iv = [0x3c; 16];
        ctx.encrypt(&mut iv, &mut []);
        ctx.decrypt(&mut iv, &mut []);
        assert_eq!(iv, [0x3c; 16]);
        // Every length is a prefix of the longest message's ciphertext, and
        // round-trips.
        let message: Vec<_> = (0..16 * 5).map(|i| (7 * i + 1) as u8).collect();
        let mut ciphertext = message.clone();
        ctx.encrypt(&mut iv, &mut ciphertext);
        for n in 0..message.len() {
            let mut iv = [0x3c; 16];
            let mut buffer = message[..n].to_vec();
            ctx.encrypt(&mut iv, &mut buffer);
            assert_eq!(buffer, ciphertext[..n]);
            let mut iv = [0x3c; 16];
            ctx.decrypt(&mut iv, &mut buffer);
            assert_eq!(buffer, message[..n]);
        }
    }
}
