//! Camellia-CBC: OpenSSL's test vectors as pyca/cryptography vendors them,
//! unmodified under vectors/; and CBC from ECB (`CamelliaEcb`, tested on
//! RFC 3713's and NTT's vectors) on every length up to a few groups of eight
//! blocks, for each key length.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use verified_garbage::camellia_cbc::{CamelliaCbc, Error};
use verified_garbage::camellia_ecb::CamelliaEcb;

use super::unhex;

/// CBC encryption from ECB, one block at a time.
fn reference(key: &[u8], iv: [u8; 16], data: &[u8]) -> Vec<u8> {
    let ecb = CamelliaEcb::new(key).unwrap();
    let mut chain = iv;
    let mut out = Vec::new();
    for block in data.chunks(16) {
        let mut b: Vec<u8> = block.iter().zip(&chain).map(|(x, y)| x ^ y).collect();
        ecb.encrypt(&mut b).unwrap();
        chain.copy_from_slice(&b);
        out.extend_from_slice(&b);
    }
    out
}

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary, leaving the last ciphertext block as the
/// chaining value.
fn check(ctx: &CamelliaCbc, iv: [u8; 16], plaintext: &[u8], ciphertext: &[u8]) {
    let after: [u8; 16] = match ciphertext.len() {
        0 => iv,
        len => ciphertext[len - 16..].try_into().unwrap(),
    };
    for offset in (0..=plaintext.len()).step_by(16) {
        let mut chain = iv;
        let mut buffer = plaintext.to_vec();
        ctx.encrypt(&mut chain, &mut buffer[..offset]).unwrap();
        ctx.encrypt(&mut chain, &mut buffer[offset..]).unwrap();
        assert_eq!(buffer, ciphertext);
        assert_eq!(chain, after);
        let mut chain = iv;
        ctx.decrypt(&mut chain, &mut buffer[..offset]).unwrap();
        ctx.decrypt(&mut chain, &mut buffer[offset..]).unwrap();
        assert_eq!(buffer, plaintext);
        assert_eq!(chain, after);
    }
}

#[test]
fn openssl_vectors() {
    let text = include_str!("../../vectors/cryptography-camellia-cbc/camellia-cbc.txt");
    let mut key_lens = Vec::new();
    for record in text.split("COUNT = ").skip(1) {
        let get = |label: &str| {
            let line = record.lines().find(|l| l.starts_with(label)).unwrap();
            unhex(line.split_once(" = ").unwrap().1.trim())
        };
        let key = get("KEY");
        let iv: [u8; 16] = get("IV").try_into().unwrap();
        key_lens.push(key.len());
        check(
            &CamelliaCbc::new(&key).unwrap(),
            iv,
            &get("PLAINTEXT"),
            &get("CIPHERTEXT"),
        );
    }
    assert_eq!(key_lens, [16, 16, 16, 16, 24, 24, 24, 24, 32, 32, 32, 32]);
}

/// Every number of blocks up to three groups of eight and a bit.
#[test]
fn from_ecb() {
    let data: Vec<u8> = (0..16 * 27).map(|i| (i * 31 + 7) as u8).collect();
    let iv: [u8; 16] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    for key_len in [16, 24, 32] {
        let key: Vec<u8> = (0..key_len).map(|i| (17 * i + 3) as u8).collect();
        let ctx = CamelliaCbc::new(&key).unwrap();
        for blocks in 0..=27 {
            let input = &data[..16 * blocks];
            check(&ctx, iv, input, &reference(&key, iv, input));
        }
    }
}

#[test]
fn errors() {
    for len in [0, 15, 17, 33] {
        assert!(matches!(
            CamelliaCbc::new(&vec![0; len]),
            Err(Error::InvalidKeyLength)
        ));
    }
    let ctx = CamelliaCbc::new(&[0; 16]).unwrap();
    for len in [1, 15, 17, 31] {
        let mut chain = [7; 16];
        let mut buffer = vec![0x5a; len];
        assert_eq!(
            ctx.encrypt(&mut chain, &mut buffer),
            Err(Error::IncompleteBlock)
        );
        assert_eq!(
            ctx.decrypt(&mut chain, &mut buffer),
            Err(Error::IncompleteBlock)
        );
        assert_eq!(buffer, vec![0x5a; len]);
        assert_eq!(chain, [7; 16]);
    }
}
