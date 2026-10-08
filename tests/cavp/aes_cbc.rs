//! NIST CAVP AES-CBC known-answer (KAT) and multi-block message (MMT)
//! vectors, with unmodified sources under vectors/.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use std::collections::BTreeMap;

use verified_garbage::aes_cbc::{AesCbc, Error};

use super::unhex;

type Operation = fn(&AesCbc, &mut [u8; 16], &mut [u8]) -> Result<(), Error>;

/// The chaining value after a message whose last ciphertext block ends
/// `ciphertext`: that block, or `iv` for an empty message.
fn last_block(iv: &[u8; 16], ciphertext: &[u8]) -> [u8; 16] {
    match ciphertext.len() {
        0 => *iv,
        n => ciphertext[n - 16..].try_into().unwrap(),
    }
}

/// Checks a vector in both directions, in one call; with `split`, also in
/// two calls split at each block boundary and one call per block, each
/// continuing from the chaining value the last left.
fn check(key: &[u8], iv: &[u8], plaintext: &[u8], ciphertext: &[u8], split: bool) {
    assert_eq!(plaintext.len(), ciphertext.len());
    let ctx = AesCbc::new(key).unwrap();
    let iv: [u8; 16] = iv.try_into().unwrap();
    let last = last_block(&iv, ciphertext);
    for (operation, input, expected) in [
        (AesCbc::encrypt as Operation, plaintext, ciphertext),
        (AesCbc::decrypt as Operation, ciphertext, plaintext),
    ] {
        let mut output = input.to_vec();
        let mut chain = iv;
        operation(&ctx, &mut chain, &mut output).unwrap();
        assert_eq!(output, expected);
        assert_eq!(chain, last);
        if split {
            for offset in (0..=input.len()).step_by(16) {
                let mut output = input.to_vec();
                let mut chain = iv;
                operation(&ctx, &mut chain, &mut []).unwrap();
                assert_eq!(chain, iv);
                operation(&ctx, &mut chain, &mut output[..offset]).unwrap();
                operation(&ctx, &mut chain, &mut output[offset..]).unwrap();
                assert_eq!(output, expected);
                assert_eq!(chain, last);
            }
            let mut output = input.to_vec();
            let mut chain = iv;
            for block in output.chunks_mut(16) {
                operation(&ctx, &mut chain, block).unwrap();
            }
            assert_eq!(output, expected);
            assert_eq!(chain, last);
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
fn nist_cbc() {
    let files = [
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCGFSbox128.rsp"),
            14,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCGFSbox192.rsp"),
            12,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCGFSbox256.rsp"),
            10,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCKeySbox128.rsp"),
            42,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCKeySbox192.rsp"),
            48,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCKeySbox256.rsp"),
            32,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCVarKey128.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCVarKey192.rsp"),
            384,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCVarKey256.rsp"),
            512,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCVarTxt128.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCVarTxt192.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-kat-cbc/CBCVarTxt256.rsp"),
            256,
            false,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/CBCMMT128.rsp"),
            20,
            true,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/CBCMMT192.rsp"),
            20,
            true,
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-mmt/CBCMMT256.rsp"),
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
fn limits_and_empty_input() {
    for len in 0..=40 {
        let key: Vec<_> = (0..len).map(|i| (17 * i + 3) as u8).collect();
        if !matches!(len, 16 | 24 | 32) {
            assert!(matches!(AesCbc::new(&key), Err(Error::InvalidKeyLength)));
            continue;
        }
        let ctx = AesCbc::new(&key).unwrap();
        let mut iv = [0x3c; 16];
        ctx.encrypt(&mut iv, &mut []).unwrap();
        ctx.decrypt(&mut iv, &mut []).unwrap();
        assert_eq!(iv, [0x3c; 16]);
        for n in 1usize..48 {
            if n.is_multiple_of(16) {
                continue;
            }
            let mut buffer = vec![0x5a; n];
            assert_eq!(
                ctx.encrypt(&mut iv, &mut buffer),
                Err(Error::IncompleteBlock)
            );
            assert_eq!(buffer, vec![0x5a; n]);
            assert_eq!(
                ctx.decrypt(&mut iv, &mut buffer),
                Err(Error::IncompleteBlock)
            );
            assert_eq!(buffer, vec![0x5a; n]);
            assert_eq!(iv, [0x3c; 16]);
        }
        // Many blocks in one call round-trip, and equal blocks encrypt to
        // different blocks.
        let mut buffer = vec![0xa5; 16 * 67];
        ctx.encrypt(&mut iv, &mut buffer).unwrap();
        assert!(buffer.chunks(16).skip(1).all(|b| b != &buffer[..16]));
        assert_eq!(&iv[..], &buffer[16 * 66..]);
        let mut iv = [0x3c; 16];
        ctx.decrypt(&mut iv, &mut buffer).unwrap();
        assert_eq!(buffer, vec![0xa5; 16 * 67]);
    }
}
