//! NIST CAVP AES-OFB known-answer (KAT) and multi-block message (MMT)
//! vectors, with unmodified sources under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use std::collections::BTreeMap;

use verified_garbage::aes_ofb::{AesOfb, InvalidKeyLength};

use super::unhex;

/// The block to continue from after `n` whole blocks of the vector's
/// message: the `n`-th output block, the input XOR the output's last block.
fn output_block(input: &[u8], output: &[u8], n: usize) -> [u8; 16] {
    let mut o = [0; 16];
    for i in 0..16 {
        o[i] = input[16 * (n - 1) + i] ^ output[16 * (n - 1) + i];
    }
    o
}

/// Checks a vector in both directions, in one call; with `split`, also in
/// two calls split at each block boundary, one call per block, and with the
/// message cut short at each length in its last block (§6.4's partial last
/// block).
fn check(key: &[u8], iv: &[u8], plaintext: &[u8], ciphertext: &[u8], split: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    assert_eq!(plaintext.len() % 16, 0);
    let ctx = AesOfb::new(key).unwrap();
    let iv: [u8; 16] = iv.try_into().unwrap();
    let n = plaintext.len() / 16;
    // The block to continue from after the message (no vector is empty).
    let last = output_block(plaintext, ciphertext, n);
    for (input, expected) in [(plaintext, ciphertext), (ciphertext, plaintext)] {
        let mut output = input.to_vec();
        let mut chain = iv;
        ctx.apply_keystream(&mut chain, &mut output);
        assert_eq!(output, expected);
        assert_eq!(chain, last);
        if split {
            for offset in (0..=input.len()).step_by(16) {
                let mut output = input.to_vec();
                let mut chain = iv;
                ctx.apply_keystream(&mut chain, &mut []);
                assert_eq!(chain, iv);
                ctx.apply_keystream(&mut chain, &mut output[..offset]);
                ctx.apply_keystream(&mut chain, &mut output[offset..]);
                assert_eq!(output, expected);
                assert_eq!(chain, last);
            }
            let mut output = input.to_vec();
            let mut chain = iv;
            for block in output.chunks_mut(16) {
                ctx.apply_keystream(&mut chain, block);
            }
            assert_eq!(output, expected);
            assert_eq!(chain, last);
            for len in input.len() - 15..input.len() {
                let mut output = input[..len].to_vec();
                let mut chain = iv;
                ctx.apply_keystream(&mut chain, &mut output);
                assert_eq!(output, expected[..len]);
                assert_eq!(chain, last);
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
fn nist_ofb() {
    let files = [
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBGFSbox128.rsp"),
            14,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBGFSbox192.rsp"),
            12,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBGFSbox256.rsp"),
            10,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBKeySbox128.rsp"),
            42,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBKeySbox192.rsp"),
            48,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBKeySbox256.rsp"),
            32,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBVarKey128.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBVarKey192.rsp"),
            384,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBVarKey256.rsp"),
            512,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBVarTxt128.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBVarTxt192.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-ofb/OFBVarTxt256.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/OFBMMT128.rsp"),
            20,
            true,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/OFBMMT192.rsp"),
            20,
            true,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/OFBMMT256.rsp"),
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
            assert!(matches!(AesOfb::new(&key), Err(InvalidKeyLength)));
            continue;
        }
        let ctx = AesOfb::new(&key).unwrap();
        let mut iv = [0x3c; 16];
        ctx.apply_keystream(&mut iv, &mut []);
        assert_eq!(iv, [0x3c; 16]);
        // Every length is a prefix of the longest message's keystream, and
        // round-trips.
        let mut stream = vec![0; 16 * 5];
        ctx.apply_keystream(&mut iv, &mut stream);
        for n in 0..stream.len() {
            let mut iv = [0x3c; 16];
            let mut buffer = vec![0x5a; n];
            ctx.apply_keystream(&mut iv, &mut buffer);
            let expected: Vec<_> = stream[..n].iter().map(|b| b ^ 0x5a).collect();
            assert_eq!(buffer, expected);
            let mut iv = [0x3c; 16];
            ctx.apply_keystream(&mut iv, &mut buffer);
            assert_eq!(buffer, vec![0x5a; n]);
        }
    }
}
