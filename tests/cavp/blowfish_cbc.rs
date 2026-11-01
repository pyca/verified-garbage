//! Blowfish-CBC: pyca/cryptography's vector (reformatted from Schneier's
//! test vectors), unmodified under vectors/; and CBC from ECB
//! (`BlowfishEcbEncryptor`, tested on Schneier's vectors) on every number of
//! blocks up to 27, for keys of the shortest, a middle and the longest
//! length.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::blowfish_cbc::{BlowfishCbc, Error};
use verified_garbage::blowfish_ecb::BlowfishEcbEncryptor;

use super::unhex;

/// CBC encryption from ECB, one block at a time.
fn reference(key: &[u8], iv: [u8; 8], data: &[u8]) -> Vec<u8> {
    let mut ecb = BlowfishEcbEncryptor::new(key).unwrap();
    let mut chain = iv;
    let mut out = Vec::new();
    for block in data.chunks(8) {
        let b: Vec<u8> = crate::bytes::xor(block, &chain);
        assert_eq!(ecb.update(&b, &mut chain).unwrap(), 8);
        out.extend_from_slice(&chain);
    }
    ecb.finalize().unwrap();
    out
}

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary, leaving the last ciphertext block as the
/// chaining value.
fn check(ctx: &BlowfishCbc, iv: [u8; 8], plaintext: &[u8], ciphertext: &[u8]) {
    let after: [u8; 8] = match ciphertext.len() {
        0 => iv,
        len => ciphertext[len - 8..].try_into().unwrap(),
    };
    for offset in (0..=plaintext.len()).step_by(8) {
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
fn pyca_vectors() {
    let text = crate::vectors::text("vectors/cryptography-blowfish-cbc/bf-cbc.txt");
    let mut key_lens = Vec::new();
    for record in text.split("COUNT = ").skip(1) {
        let get = |label: &str| {
            let line = record.lines().find(|l| l.starts_with(label)).unwrap();
            unhex(line.split_once(" = ").unwrap().1.trim())
        };
        let key = get("KEY");
        let iv: [u8; 8] = get("IV").try_into().unwrap();
        key_lens.push(key.len());
        check(
            &BlowfishCbc::new(&key).unwrap(),
            iv,
            &get("PLAINTEXT"),
            &get("CIPHERTEXT"),
        );
    }
    assert_eq!(key_lens, [16]);
}

/// Every number of blocks up to 27.
#[test]
fn from_ecb() {
    let data: Vec<u8> = crate::bytes::pattern(8 * 27, 31, 7);
    let iv: [u8; 8] = crate::bytes::pattern_array(11, 5);
    for key_len in [4, 16, 56] {
        let key: Vec<u8> = crate::bytes::pattern(key_len, 17, 3);
        let ctx = BlowfishCbc::new(&key).unwrap();
        for blocks in 0..=27 {
            let input = &data[..8 * blocks];
            check(&ctx, iv, input, &reference(&key, iv, input));
        }
    }
}

#[test]
fn errors() {
    for len in [0, 1, 3, 57, 64] {
        assert!(matches!(
            BlowfishCbc::new(&vec![0; len]),
            Err(Error::InvalidKeyLength)
        ));
    }
    let ctx = BlowfishCbc::new(&[0; 16]).unwrap();
    for len in [1, 15, 17, 31] {
        let mut chain = [7; 8];
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
        assert_eq!(chain, [7; 8]);
    }
}
