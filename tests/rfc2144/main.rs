//! CAST5 (CAST-128) ECB: the vectors of RFC 2144 Appendix B.1, read from the
//! byte-for-byte vendored RFC, with Botan's published CAST-128 vectors and
//! pyca/cryptography's CAST5-CBC vectors (chained here through ECB), each
//! vendored under `vectors/` (see `vectors/sources/`).

#![cfg(target_arch = "x86_64")]

use verified_garbage::cast5_ecb::{Cast5Ecb, Error};

fn unhex(text: &str) -> Vec<u8> {
    let hex: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    assert_eq!(hex.len() % 2, 0);
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
        .collect()
}

/// Encrypts `plaintext` to `ciphertext` and back, whole and a block at a
/// time.
fn check(key: &[u8], plaintext: &[u8], ciphertext: &[u8]) {
    let cipher = Cast5Ecb::new(key).unwrap();
    let mut data = plaintext.to_vec();
    cipher.encrypt(&mut data).unwrap();
    assert_eq!(data, ciphertext);
    cipher.decrypt(&mut data).unwrap();
    assert_eq!(data, plaintext);
    for (p, c) in plaintext.chunks(8).zip(ciphertext.chunks(8)) {
        let mut block = p.to_vec();
        cipher.encrypt(&mut block).unwrap();
        assert_eq!(block, c);
        cipher.decrypt(&mut block).unwrap();
        assert_eq!(block, p);
    }
}

#[test]
fn rfc2144_b1() {
    let text = include_str!("../../vectors/rfc2144/rfc2144.txt");
    let section = text
        .split_once("B.1. Single Plaintext-Key-Ciphertext Sets")
        .unwrap()
        .1
        .split_once("B.2. Full Maintenance Test")
        .unwrap()
        .0;
    let mut count = 0;
    for record in section.split("-bit").skip(1) {
        let mut lines = record.lines().map(str::trim);
        // The key as given, then (for a short key) padded with zeros.
        let key = unhex(
            lines
                .next()
                .unwrap()
                .split_once("key")
                .unwrap()
                .1
                .trim()
                .trim_start_matches('='),
        );
        let field = |name: &str| {
            let line = record
                .lines()
                .map(str::trim)
                .find(|l| l.starts_with(name))
                .unwrap();
            unhex(line.split_once('=').unwrap().1)
        };
        check(&key, &field("plaintext"), &field("ciphertext"));
        count += 1;
    }
    assert_eq!(count, 3);
}

#[test]
fn botan() {
    let text = include_str!("../../vectors/botan-cast128/cast128.vec");
    let mut count = 0;
    for record in text.split("\n\n") {
        let field = |name: &str| {
            record
                .lines()
                .find_map(|l| l.strip_prefix(name)?.trim().strip_prefix('='))
                .map(unhex)
        };
        let Some(key) = field("Key") else { continue };
        check(&key, &field("In").unwrap(), &field("Out").unwrap());
        count += 1;
    }
    assert_eq!(count, 48);
}

#[test]
fn cryptography_cbc() {
    let text = include_str!("../../vectors/cryptography-cast5/cast5-cbc.txt");
    let mut count = 0;
    for record in text.split("\n\n") {
        let field = |name: &str| {
            record
                .lines()
                .find_map(|l| l.strip_prefix(name)?.trim().strip_prefix('='))
                .map(unhex)
        };
        let Some(key) = field("KEY") else { continue };
        let iv = field("IV").unwrap();
        let plaintext = field("PLAINTEXT").unwrap();
        let ciphertext = field("CIPHERTEXT").unwrap();
        let cipher = Cast5Ecb::new(&key).unwrap();
        let mut chain = iv.clone();
        for (p, c) in plaintext.chunks(8).zip(ciphertext.chunks(8)) {
            let mut block: Vec<u8> = p.iter().zip(&chain).map(|(a, b)| a ^ b).collect();
            cipher.encrypt(&mut block).unwrap();
            assert_eq!(block, c);
            cipher.decrypt(&mut block).unwrap();
            let decrypted: Vec<u8> = block.iter().zip(&chain).map(|(a, b)| a ^ b).collect();
            assert_eq!(decrypted, p);
            chain = c.to_vec();
        }
        count += 1;
    }
    assert_eq!(count, 20);
}

#[test]
fn errors_and_empty_input() {
    for len in [0, 4, 17, 32] {
        assert_eq!(
            Cast5Ecb::new(&vec![0; len]).err(),
            Some(Error::InvalidKeyLength)
        );
    }
    let cipher = Cast5Ecb::new(&[1; 16]).unwrap();
    for len in [1, 7, 9, 15] {
        let mut data = vec![0xa5; len];
        assert_eq!(cipher.encrypt(&mut data), Err(Error::IncompleteBlock));
        assert_eq!(cipher.decrypt(&mut data), Err(Error::IncompleteBlock));
        assert!(data.iter().all(|&b| b == 0xa5));
    }
    cipher.encrypt(&mut []).unwrap();
    cipher.decrypt(&mut []).unwrap();
}
