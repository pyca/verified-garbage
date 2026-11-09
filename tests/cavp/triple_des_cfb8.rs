//! Triple DES-CFB8: NIST CAVP's multi-block message tests, unmodified under
//! vectors/, whole and split at every byte, for each key length.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cipher::triple_des::{TripleDesCfb8Decryptor, TripleDesCfb8Encryptor};
use verified_garbage::error::InvalidKeyLength;

use verified_garbage_test_vectors::{cavp_records, unhex};

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every byte.
fn check(key: &[u8], iv: [u8; 8], plaintext: &[u8], ciphertext: &[u8]) {
    for offset in 0..=plaintext.len() {
        let mut buffer = plaintext.to_vec();
        let mut encryptor = TripleDesCfb8Encryptor::new(key, &iv).unwrap();
        encryptor.encrypt(&mut buffer[..offset]);
        encryptor.encrypt(&mut buffer[offset..]);
        assert_eq!(buffer, ciphertext);
        let mut decryptor = TripleDesCfb8Decryptor::new(key, &iv).unwrap();
        decryptor.decrypt(&mut buffer[..offset]);
        decryptor.decrypt(&mut buffer[offset..]);
        assert_eq!(buffer, plaintext);
    }
}

fn check_file(text: &str) -> usize {
    let mut count = 0;
    for fields in cavp_records(text) {
        let mut key = unhex(fields["KEY1"]);
        key.extend(unhex(fields["KEY2"]));
        key.extend(unhex(fields["KEY3"]));
        let iv: [u8; 8] = unhex(fields["IV"]).try_into().unwrap();
        let plaintext = unhex(fields["PLAINTEXT"]);
        let ciphertext = unhex(fields["CIPHERTEXT"]);
        check(&key, iv, &plaintext, &ciphertext);
        if key[..8] == key[16..] {
            check(&key[..16], iv, &plaintext, &ciphertext);
        }
        count += 1;
    }
    count
}

#[test]
fn cavp_mmt() {
    assert_eq!(
        check_file(&crate::vectors::text(
            "vectors/nist-cavp-tdes-mmt/TCFB8MMT2.rsp"
        )),
        10
    );
    assert_eq!(
        check_file(&crate::vectors::text(
            "vectors/nist-cavp-tdes-mmt/TCFB8MMT3.rsp"
        )),
        20
    );
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 32] {
        assert_eq!(
            TripleDesCfb8Encryptor::new(&vec![0; len], &[0; 8]).err(),
            Some(InvalidKeyLength)
        );
        assert_eq!(
            TripleDesCfb8Decryptor::new(&vec![0; len], &[0; 8]).err(),
            Some(InvalidKeyLength)
        );
    }
}
