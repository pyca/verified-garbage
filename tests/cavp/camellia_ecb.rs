//! Published Camellia vectors: RFC 3713's example data and NTT's
//! known-answer tests as pyca/cryptography vendors them; unmodified sources
//! and provenance live under vectors/.

#![cfg(target_arch = "x86_64")]

use verified_garbage::camellia_ecb::{CamelliaEcb, Error};

use super::unhex;

/// `key` encrypts `plaintext` (any number of blocks) to `ciphertext` and
/// decrypts it back.
fn check(key: &[u8], plaintext: &[u8], ciphertext: &[u8]) {
    let ecb = CamelliaEcb::new(key).unwrap();
    let mut buffer = plaintext.to_vec();
    ecb.encrypt(&mut buffer).unwrap();
    assert_eq!(buffer, ciphertext);
    ecb.decrypt(&mut buffer).unwrap();
    assert_eq!(buffer, plaintext);
}

/// The hex digits of a field's value, which may continue on lines that
/// start with `:`.
fn field(lines: &[&str], label: &str) -> Vec<u8> {
    let start = lines
        .iter()
        .position(|line| line.trim_start().starts_with(label))
        .unwrap();
    let mut hex: String = lines[start].split_once(':').unwrap().1.replace(' ', "");
    for line in &lines[start + 1..] {
        match line.trim_start().strip_prefix(':') {
            Some(rest) => hex.push_str(&rest.replace(' ', "")),
            None => break,
        }
    }
    unhex(&hex)
}

#[test]
fn rfc3713() {
    let text = include_str!("../../vectors/rfc3713/rfc3713.txt");
    let excerpt = text
        .split("Appendix A.  Example Data of Camellia")
        .nth(1)
        .unwrap();
    let mut count = 0;
    for (bits, record) in [128, 192, 256]
        .into_iter()
        .zip(excerpt.split("-bit key").skip(1))
    {
        let lines: Vec<&str> = record.lines().collect();
        let key = field(&lines, "Key");
        assert_eq!(key.len() * 8, bits);
        check(
            &key,
            &field(&lines, "Plaintext"),
            &field(&lines, "Ciphertext"),
        );
        count += 1;
    }
    assert_eq!(count, 3);
}

/// A key and its plaintext and ciphertext blocks.
type Record = (Vec<u8>, Vec<(Vec<u8>, Vec<u8>)>);

/// The records of each `K No.` line.
fn ntt(text: &str) -> Vec<Record> {
    let mut out: Vec<Record> = Vec::new();
    let mut plaintext = None;
    for line in text.lines() {
        let Some((label, value)) = line.split_once(" : ") else {
            continue;
        };
        let value = unhex(&value.replace(' ', ""));
        match label.split_whitespace().next().unwrap() {
            "K" => out.push((value, Vec::new())),
            "P" => plaintext = Some(value),
            label => {
                assert_eq!(label, "C");
                let p = plaintext.take().unwrap();
                out.last_mut().unwrap().1.push((p, value));
            }
        }
    }
    out
}

/// Each block alone, all the blocks of each key at once, and its first
/// 1 to 17 blocks (fewer than, as many as and more than a group of eight).
fn check_ntt(text: &str, key_len: usize) {
    let records = ntt(text);
    assert_eq!(records.len(), 10);
    for (key, blocks) in &records {
        assert_eq!(key.len(), key_len);
        assert_eq!(blocks.len(), 128);
        for (p, c) in blocks {
            check(key, p, c);
        }
        for n in (1..=17).chain([128]) {
            let p: Vec<u8> = blocks[..n].iter().flat_map(|(p, _)| p.clone()).collect();
            let c: Vec<u8> = blocks[..n].iter().flat_map(|(_, c)| c.clone()).collect();
            check(key, &p, &c);
        }
    }
}

#[test]
fn ntt_128() {
    check_ntt(
        include_str!("../../vectors/cryptography-camellia-128/camellia-128-ecb.txt"),
        16,
    );
}

#[test]
fn ntt_192() {
    check_ntt(
        include_str!("../../vectors/cryptography-camellia-192/camellia-192-ecb.txt"),
        24,
    );
}

#[test]
fn ntt_256() {
    check_ntt(
        include_str!("../../vectors/cryptography-camellia-256/camellia-256-ecb.txt"),
        32,
    );
}

#[test]
fn invalid_key_lengths() {
    for len in [0, 1, 8, 15, 17, 23, 25, 31, 33, 64] {
        assert_eq!(
            CamelliaEcb::new(&vec![0; len]).err(),
            Some(Error::InvalidKeyLength)
        );
    }
}

#[test]
fn empty_and_incomplete() {
    let ecb = CamelliaEcb::new(&[0; 16]).unwrap();
    assert_eq!(ecb.encrypt(&mut []), Ok(()));
    assert_eq!(ecb.decrypt(&mut []), Ok(()));
    for len in [1, 8, 15, 17, 31, 33] {
        let mut buffer = vec![0xa5; len];
        assert_eq!(ecb.encrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert_eq!(ecb.decrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert!(buffer.iter().all(|&b| b == 0xa5));
    }
}
