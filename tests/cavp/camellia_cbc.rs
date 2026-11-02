//! Camellia-CBC: OpenSSL's test vectors as pyca/cryptography vendors them,
//! unmodified under vectors/, whole and split at every block.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::camellia_cbc::{CamelliaCbc, Error};

use verified_garbage_test_vectors::unhex;

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary, leaving the last ciphertext block as the
/// chaining value.
fn check(ctx: &CamelliaCbc, iv: [u8; 16], plaintext: &[u8], ciphertext: &[u8]) {
    let after: [u8; 16] = *ciphertext.last_chunk().unwrap();
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
    let text = crate::vectors::text("vectors/cryptography-camellia-cbc/camellia-cbc.txt");
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
