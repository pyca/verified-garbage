//! SEED-CBC: RFC 4196's vectors as pyca/cryptography reformats them,
//! unmodified under vectors/, whole and split at every block.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::error::IncompleteBlock;

use verified_garbage::cipher::seed::{SeedCbcDecryptor, SeedCbcEncryptor};

use verified_garbage_test_vectors::unhex;

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary.
fn check(key: &[u8; 16], iv: [u8; 16], plaintext: &[u8], ciphertext: &[u8]) {
    for offset in (0..=plaintext.len()).step_by(16) {
        let mut buffer = plaintext.to_vec();
        let mut encryptor = SeedCbcEncryptor::new(key, &iv);
        encryptor.encrypt(&mut buffer[..offset]).unwrap();
        encryptor.encrypt(&mut buffer[offset..]).unwrap();
        assert_eq!(buffer, ciphertext);
        let mut decryptor = SeedCbcDecryptor::new(key, &iv);
        decryptor.decrypt(&mut buffer[..offset]).unwrap();
        decryptor.decrypt(&mut buffer[offset..]).unwrap();
        assert_eq!(buffer, plaintext);
    }
}

#[test]
fn pyca_vectors() {
    let text = crate::vectors::text("vectors/cryptography-seed-cbc/rfc-4196.txt");
    let mut key_lens = Vec::new();
    for record in text.split("COUNT = ").skip(1) {
        let get = |label: &str| {
            let line = record.lines().find(|l| l.starts_with(label)).unwrap();
            unhex(line.split_once(" = ").unwrap().1.trim())
        };
        let key: [u8; 16] = get("KEY").try_into().unwrap();
        let iv: [u8; 16] = get("IV").try_into().unwrap();
        key_lens.push(key.len());
        check(&key, iv, &get("PLAINTEXT"), &get("CIPHERTEXT"));
    }
    assert_eq!(key_lens, [16; 2]);
}

#[test]
fn errors() {
    let key = [0; 16];
    let mut encryptor = SeedCbcEncryptor::new(&key, &[7; 16]);
    let mut decryptor = SeedCbcDecryptor::new(&key, &[7; 16]);
    for len in [1, 15, 17, 31] {
        let mut buffer = vec![0x5a; len];
        assert_eq!(encryptor.encrypt(&mut buffer), Err(IncompleteBlock));
        assert_eq!(decryptor.decrypt(&mut buffer), Err(IncompleteBlock));
        assert_eq!(buffer, vec![0x5a; len]);
    }
    // The failed calls changed nothing.
    let mut buffer = [0x5a; 32];
    let mut expected = buffer;
    SeedCbcEncryptor::new(&key, &[7; 16])
        .encrypt(&mut expected)
        .unwrap();
    encryptor.encrypt(&mut buffer).unwrap();
    assert_eq!(buffer, expected);
    decryptor.decrypt(&mut buffer).unwrap();
    assert_eq!(buffer, [0x5a; 32]);
}
