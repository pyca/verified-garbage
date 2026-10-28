//! SEED-CBC: RFC 4196's vectors as pyca/cryptography reformats them, unmodified under vectors/; and CBC from ECB
//! (`SeedEcb`, tested on RFC 4269's vectors) on every number of blocks up to 40 (two batches of sixteen and a bit).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::seed_cbc::{Error, SeedCbc};
use verified_garbage::seed_ecb::SeedEcb;

use super::unhex;

/// CBC encryption from ECB, one block at a time.
fn reference(key: &[u8], iv: [u8; 16], data: &[u8]) -> Vec<u8> {
    let ecb = SeedEcb::new(key.try_into().unwrap());
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
fn check(ctx: &SeedCbc, iv: [u8; 16], plaintext: &[u8], ciphertext: &[u8]) {
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
fn pyca_vectors() {
    let text = include_str!("../../vectors/cryptography-seed-cbc/rfc-4196.txt");
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
            &SeedCbc::new(&key).unwrap(),
            iv,
            &get("PLAINTEXT"),
            &get("CIPHERTEXT"),
        );
    }
    assert_eq!(key_lens, [16; 2]);
}

/// Every number of blocks up to 40: two batches of sixteen and a bit.
#[test]
fn from_ecb() {
    let data: Vec<u8> = (0..16 * 40).map(|i| (i * 31 + 7) as u8).collect();
    let iv: [u8; 16] = core::array::from_fn(|i| (i * 11 + 5) as u8);
    {
        let key: Vec<u8> = (0..16).map(|i| (17 * i + 3) as u8).collect();
        let ctx = SeedCbc::new(&key).unwrap();
        for blocks in 0..=40 {
            let input = &data[..16 * blocks];
            check(&ctx, iv, input, &reference(&key, iv, input));
        }
    }
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 24, 32] {
        assert!(matches!(
            SeedCbc::new(&vec![0; len]),
            Err(Error::InvalidKeyLength)
        ));
    }
    let ctx = SeedCbc::new(&[0; 16]).unwrap();
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
