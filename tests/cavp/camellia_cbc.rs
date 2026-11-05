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

use verified_garbage::camellia_cbc::{CamelliaCbcDecryptor, CamelliaCbcEncryptor, Error};

use verified_garbage_test_vectors::unhex;

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary.
fn check(key: &[u8], iv: [u8; 16], plaintext: &[u8], ciphertext: &[u8]) {
    for offset in (0..=plaintext.len()).step_by(16) {
        let mut buffer = plaintext.to_vec();
        let mut encryptor = CamelliaCbcEncryptor::new(key, &iv).unwrap();
        encryptor.encrypt(&mut buffer[..offset]).unwrap();
        encryptor.encrypt(&mut buffer[offset..]).unwrap();
        assert_eq!(buffer, ciphertext);
        let mut decryptor = CamelliaCbcDecryptor::new(key, &iv).unwrap();
        decryptor.decrypt(&mut buffer[..offset]).unwrap();
        decryptor.decrypt(&mut buffer[offset..]).unwrap();
        assert_eq!(buffer, plaintext);
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
        check(&key, iv, &get("PLAINTEXT"), &get("CIPHERTEXT"));
    }
    assert_eq!(key_lens, [16, 16, 16, 16, 24, 24, 24, 24, 32, 32, 32, 32]);
}

#[test]
fn errors() {
    for len in [0, 15, 17, 33] {
        assert!(matches!(
            CamelliaCbcEncryptor::new(&vec![0; len], &[0; 16]),
            Err(Error::InvalidKeyLength)
        ));
        assert!(matches!(
            CamelliaCbcDecryptor::new(&vec![0; len], &[0; 16]),
            Err(Error::InvalidKeyLength)
        ));
    }
    let key = [0; 16];
    let mut encryptor = CamelliaCbcEncryptor::new(&key, &[7; 16]).unwrap();
    let mut decryptor = CamelliaCbcDecryptor::new(&key, &[7; 16]).unwrap();
    for len in [1, 15, 17, 31] {
        let mut buffer = vec![0x5a; len];
        assert_eq!(encryptor.encrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert_eq!(decryptor.decrypt(&mut buffer), Err(Error::IncompleteBlock));
        assert_eq!(buffer, vec![0x5a; len]);
    }
    // The failed calls changed nothing.
    let mut buffer = [0x5a; 32];
    let mut expected = buffer;
    CamelliaCbcEncryptor::new(&key, &[7; 16])
        .unwrap()
        .encrypt(&mut expected)
        .unwrap();
    encryptor.encrypt(&mut buffer).unwrap();
    assert_eq!(buffer, expected);
    decryptor.decrypt(&mut buffer).unwrap();
    assert_eq!(buffer, [0x5a; 32]);
}
