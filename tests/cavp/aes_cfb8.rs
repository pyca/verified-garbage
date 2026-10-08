//! NIST CAVP AES-CFB8 known-answer (KAT) and multi-block message (MMT)
//! vectors, with unmodified sources under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use std::collections::BTreeMap;

use verified_garbage::aes_cfb8::{AesCfb8, InvalidKeyLength};

use super::unhex;

/// `AesCfb8::encrypt` or `AesCfb8::decrypt`.
type Direction = fn(&AesCfb8, &mut [u8; 16], &mut [u8]);

/// The input block after `ciphertext` from `iv`: the last 16 bytes of `iv`
/// followed by `ciphertext`.
fn next(iv: &[u8; 16], ciphertext: &[u8]) -> [u8; 16] {
    let all = [&iv[..], ciphertext].concat();
    all[all.len() - 16..].try_into().unwrap()
}

/// Checks a vector in both directions, in one call; with `split`, also in
/// two calls split at each length, one call per byte, and with the message
/// cut short at each length.
fn check(key: &[u8], iv: &[u8], plaintext: &[u8], ciphertext: &[u8], split: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    let ctx = AesCfb8::new(key).unwrap();
    let iv: [u8; 16] = iv.try_into().unwrap();
    let last = next(&iv, ciphertext);
    let directions: [(Direction, &[u8], &[u8]); 2] = [
        (AesCfb8::encrypt, plaintext, ciphertext),
        (AesCfb8::decrypt, ciphertext, plaintext),
    ];
    for (f, input, expected) in directions {
        let mut output = input.to_vec();
        let mut chain = iv;
        f(&ctx, &mut chain, &mut output);
        assert_eq!(output, expected);
        assert_eq!(chain, last);
        if split {
            for offset in 0..=input.len() {
                let mut output = input.to_vec();
                let mut chain = iv;
                f(&ctx, &mut chain, &mut []);
                assert_eq!(chain, iv);
                f(&ctx, &mut chain, &mut output[..offset]);
                assert_eq!(chain, next(&iv, &ciphertext[..offset]));
                f(&ctx, &mut chain, &mut output[offset..]);
                assert_eq!(output, expected);
                assert_eq!(chain, last);
            }
            let mut output = input.to_vec();
            let mut chain = iv;
            for byte in output.chunks_mut(1) {
                f(&ctx, &mut chain, byte);
            }
            assert_eq!(output, expected);
            assert_eq!(chain, last);
            for len in 0..input.len() {
                let mut output = input[..len].to_vec();
                let mut chain = iv;
                f(&ctx, &mut chain, &mut output);
                assert_eq!(output, expected[..len]);
                assert_eq!(chain, next(&iv, &ciphertext[..len]));
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
fn nist_cfb8() {
    let files = [
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8GFSbox128.rsp"),
            14,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8GFSbox192.rsp"),
            12,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8GFSbox256.rsp"),
            10,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8KeySbox128.rsp"),
            42,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8KeySbox192.rsp"),
            48,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8KeySbox256.rsp"),
            32,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8VarKey128.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8VarKey192.rsp"),
            384,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8VarKey256.rsp"),
            512,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8VarTxt128.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8VarTxt192.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cfb8/CFB8VarTxt256.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/CFB8MMT128.rsp"),
            20,
            true,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/CFB8MMT192.rsp"),
            20,
            true,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/CFB8MMT256.rsp"),
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
            assert!(matches!(AesCfb8::new(&key), Err(InvalidKeyLength)));
            continue;
        }
        let ctx = AesCfb8::new(&key).unwrap();
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
            assert_eq!(iv, next(&[0x3c; 16], &ciphertext[..n]));
            let mut iv = [0x3c; 16];
            ctx.decrypt(&mut iv, &mut buffer);
            assert_eq!(buffer, message[..n]);
        }
    }
}
