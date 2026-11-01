//! IDEA-CBC: pyca/cryptography's vectors (derived from the AESVS MMT data,
//! verified against Botan), unmodified under vectors/; and CBC from ECB
//! (`IdeaEcb`, tested on the NESSIE vectors) on every number of blocks up to 27.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::idea_cbc::{Error, IdeaCbc};
use verified_garbage::idea_ecb::IdeaEcb;

use verified_garbage_test_vectors::unhex;

/// CBC encryption from ECB, one block at a time.
fn reference(key: &[u8], iv: [u8; 8], data: &[u8]) -> Vec<u8> {
    let ecb = IdeaEcb::new(key).unwrap();
    let mut chain = iv;
    let mut out = Vec::new();
    for block in data.chunks(8) {
        let mut b: Vec<u8> = crate::bytes::xor(block, &chain);
        ecb.encrypt(&mut b).unwrap();
        chain.copy_from_slice(&b);
        out.extend_from_slice(&b);
    }
    out
}

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary, leaving the last ciphertext block as the
/// chaining value.
fn check(ctx: &IdeaCbc, iv: [u8; 8], plaintext: &[u8], ciphertext: &[u8]) {
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
    let text = crate::vectors::text("vectors/cryptography-idea-cbc/idea-cbc.txt");
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
            &IdeaCbc::new(&key).unwrap(),
            iv,
            &get("PLAINTEXT"),
            &get("CIPHERTEXT"),
        );
    }
    assert_eq!(key_lens, [16; 20]);
}

/// Every number of blocks up to 27.
#[test]
fn from_ecb() {
    let data: Vec<u8> = crate::bytes::pattern(8 * 27, 31, 7);
    let iv: [u8; 8] = crate::bytes::pattern_array(11, 5);
    {
        let key: Vec<u8> = crate::bytes::pattern(16, 17, 3);
        let ctx = IdeaCbc::new(&key).unwrap();
        for blocks in 0..=27 {
            let input = &data[..8 * blocks];
            check(&ctx, iv, input, &reference(&key, iv, input));
        }
    }
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 24, 32] {
        assert!(matches!(
            IdeaCbc::new(&vec![0; len]),
            Err(Error::InvalidKeyLength)
        ));
    }
    let ctx = IdeaCbc::new(&[0; 16]).unwrap();
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
