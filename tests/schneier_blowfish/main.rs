//! Blowfish-ECB against Eric Young's test vectors, as Schneier publishes
//! them, read from the byte-for-byte vendored file: every ECB record, every
//! `set_key` record (and the rejection of keys shorter than 32 bits); its
//! CBC record, as pyca/cryptography reformats it, tests CBC itself, in
//! `tests/cavp/blowfish_cbc.rs`. Then ECB of many blocks at once against one
//! block at a time, and the streaming wrapper's splits and errors.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cipher::blowfish::BlowfishEcb;
use verified_garbage::error::{IncompleteBlock, InvalidKeyLength};
use verified_garbage_test_vectors::unhex_spaced;

/// The vectors' file (`crate::vectors`).
fn text() -> String {
    crate::vectors::text("vectors/schneier-blowfish-vectors/vectors-2.txt")
}

fn encrypt(key: &[u8], input: &[u8]) -> Vec<u8> {
    let cipher = BlowfishEcb::new(key).unwrap();
    let mut output = input.to_vec();
    cipher.encrypt(&mut output).unwrap();
    output
}

fn decrypt(key: &[u8], input: &[u8]) -> Vec<u8> {
    let cipher = BlowfishEcb::new(key).unwrap();
    let mut output = input.to_vec();
    cipher.decrypt(&mut output).unwrap();
    output
}

/// The lines of the file after the one starting with `start`, up to the
/// one starting with `end`, trimmed (the file has CRLF line endings).
fn section(start: &str, end: &str) -> Vec<String> {
    text()
        .lines()
        .map(str::trim)
        .skip_while(|line| !line.starts_with(start))
        .skip(1)
        .take_while(|line| !line.starts_with(end))
        .map(str::to_owned)
        .collect()
}

#[test]
fn ecb_records() {
    let mut count = 0;
    for line in section("key bytes", "set_key test data") {
        let fields: Vec<&str> = line.split_whitespace().collect();
        let [key, clear, cipher]: [&str; 3] = fields.try_into().unwrap();
        let (key, clear, cipher) = (unhex_spaced(key), unhex_spaced(clear), unhex_spaced(cipher));
        assert_eq!(encrypt(&key, &clear), cipher);
        assert_eq!(decrypt(&key, &cipher), clear);
        count += 1;
    }
    assert_eq!(count, 34);
}

#[test]
fn set_key_records() {
    let records = section("set_key test data", "chaining mode test data");
    let mut lines = records.into_iter();
    let clear = unhex_spaced(lines.next().unwrap().strip_prefix("data[8]= ").unwrap());
    let mut count = 0;
    for line in lines.filter(|line| !line.is_empty()) {
        let (cipher, key) = line.strip_prefix("c=").unwrap().split_once(" k[").unwrap();
        let (length, key) = key.split_once("]=").unwrap();
        let length: usize = length.trim().parse().unwrap();
        let (cipher, key) = (unhex_spaced(cipher), unhex_spaced(key));
        assert_eq!(key.len(), length);
        if length < 4 {
            assert!(matches!(BlowfishEcb::new(&key), Err(InvalidKeyLength)));
        } else {
            assert_eq!(encrypt(&key, &clear), cipher);
            assert_eq!(decrypt(&key, &cipher), clear);
        }
        count += 1;
    }
    assert_eq!(count, 24);
}

/// Many blocks at once match one block at a time, for every count up to
/// 50, with the longest key.
#[test]
fn many_blocks() {
    let key: Vec<u8> = crate::bytes::pattern(56, 37, 11);
    let data: Vec<u8> = crate::bytes::pattern(8 * 50, 101, 7);
    let mut single = Vec::new();
    for block in data.chunks(8) {
        single.extend(encrypt(&key, block));
    }
    for n in 0..=50 {
        let cipher = encrypt(&key, &data[..8 * n]);
        assert_eq!(cipher, single[..8 * n]);
        assert_eq!(decrypt(&key, &cipher), data[..8 * n]);
    }
}

/// One expanded key supports both directions and repeated calls on unaligned
/// slices, without touching the surrounding bytes.
#[test]
fn in_place() {
    let key = [7; 16];
    let cipher = BlowfishEcb::new(&key).unwrap();
    let data = crate::bytes::pattern(8 * 20, 13, 5);
    let whole = encrypt(&key, &data);
    for offset in 0..8 {
        for split in (0..=data.len()).step_by(8) {
            let mut buffer = vec![0xa5; offset + data.len() + 8];
            buffer[offset..offset + data.len()].copy_from_slice(&data);
            let (first, second) = buffer[offset..offset + data.len()].split_at_mut(split);
            cipher.encrypt(first).unwrap();
            cipher.encrypt(second).unwrap();
            assert_eq!(&buffer[offset..offset + data.len()], whole);
            cipher
                .decrypt(&mut buffer[offset..offset + data.len()])
                .unwrap();
            assert_eq!(&buffer[offset..offset + data.len()], data);
            assert_eq!(&buffer[..offset], vec![0xa5; offset]);
            assert_eq!(&buffer[offset + data.len()..], [0xa5; 8]);
        }
    }
}

#[test]
fn errors() {
    for length in [0, 3, 57, 100] {
        assert!(matches!(
            BlowfishEcb::new(&vec![1; length]),
            Err(InvalidKeyLength)
        ));
    }
    let cipher = BlowfishEcb::new(&[7; 16]).unwrap();
    for length in (1..24).filter(|n| n % 8 != 0) {
        let mut buffer = vec![0xa5; length];
        assert_eq!(cipher.encrypt(&mut buffer), Err(IncompleteBlock));
        assert_eq!(buffer, vec![0xa5; length]);
        assert_eq!(cipher.decrypt(&mut buffer), Err(IncompleteBlock));
        assert_eq!(buffer, vec![0xa5; length]);
    }
    assert_eq!(cipher.encrypt(&mut []), Ok(()));
    assert_eq!(cipher.decrypt(&mut []), Ok(()));
}
