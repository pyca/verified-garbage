//! Camellia-CFB128: OpenSSL's test vectors as pyca/cryptography vendors
//! them, unmodified under vectors/, truncated and split (`tests/modes.rs`).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::error::InvalidKeyLength;

use verified_garbage::cipher::camellia::{CamelliaCfb128Decryptor, CamelliaCfb128Encryptor};

use verified_garbage_test_vectors::unhex;

#[test]
fn openssl_vectors() {
    let text = crate::vectors::text("vectors/cryptography-camellia-cfb/camellia-cfb.txt");
    let mut key_lens = Vec::new();
    for record in text.split("COUNT = ").skip(1) {
        let get = |label: &str| {
            let line = record.lines().find(|l| l.starts_with(label)).unwrap();
            unhex(line.split_once(" = ").unwrap().1.trim())
        };
        let key = get("KEY");
        let iv: [u8; 16] = get("IV").try_into().unwrap();
        let (plaintext, ciphertext) = (get("PLAINTEXT"), get("CIPHERTEXT"));
        key_lens.push(key.len());
        let vector = (&plaintext[..], &ciphertext[..]);
        crate::modes::check(
            iv,
            vector,
            &|iv| CamelliaCfb128Encryptor::new(&key, iv).unwrap(),
            CamelliaCfb128Encryptor::encrypt,
            CamelliaCfb128Encryptor::encrypt_final,
        );
        crate::modes::check(
            iv,
            (&ciphertext, &plaintext),
            &|iv| CamelliaCfb128Decryptor::new(&key, iv).unwrap(),
            CamelliaCfb128Decryptor::decrypt,
            CamelliaCfb128Decryptor::decrypt_final,
        );
    }
    assert_eq!(key_lens, [16, 16, 16, 16, 24, 24, 24, 24, 32, 32, 32, 32]);
}

#[test]
fn errors() {
    for len in [0, 15, 17, 33] {
        assert_eq!(
            CamelliaCfb128Encryptor::new(&vec![0; len], &[0; 16]).err(),
            Some(InvalidKeyLength)
        );
        assert_eq!(
            CamelliaCfb128Decryptor::new(&vec![0; len], &[0; 16]).err(),
            Some(InvalidKeyLength)
        );
    }
}

/// Decryption in place, which must read each ciphertext block before
/// overwriting it, of every vector, with unaligned data and IV buffers and
/// guards around both.
#[test]
fn decrypt_unaligned() {
    let text = crate::vectors::text("vectors/cryptography-camellia-cfb/camellia-cfb.txt");
    for record in text.split("COUNT = ").skip(1) {
        let get = |label: &str| {
            let line = record.lines().find(|l| l.starts_with(label)).unwrap();
            unhex(line.split_once(" = ").unwrap().1.trim())
        };
        let iv: [u8; 16] = get("IV").try_into().unwrap();
        let (plaintext, ciphertext) = (get("PLAINTEXT"), get("CIPHERTEXT"));
        crate::modes::check_unaligned(
            iv,
            (&ciphertext, &plaintext),
            &|iv| CamelliaCfb128Decryptor::new(&get("KEY"), iv).unwrap(),
            CamelliaCfb128Decryptor::decrypt_final,
        );
    }
}
