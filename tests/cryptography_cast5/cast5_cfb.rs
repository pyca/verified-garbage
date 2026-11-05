#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::cast5_cfb::{Cast5Cfb64Decryptor, Cast5Cfb64Encryptor, Error};

/// The vectors in both directions, truncated, in pieces and with a partial
/// last segment (`crate::modes::check`).
#[test]
fn vectors() {
    let records = super::records(&crate::vectors::text(
        "vectors/cryptography-cast5-cfb/cast5-cfb.txt",
    ));
    assert_eq!(records.len(), 20);
    for (key, iv, plaintext, ciphertext) in records {
        crate::modes::check(
            iv,
            (&plaintext, &ciphertext),
            &|iv| Cast5Cfb64Encryptor::new(&key, iv).unwrap(),
            Cast5Cfb64Encryptor::encrypt,
            Cast5Cfb64Encryptor::encrypt_final,
        );
        crate::modes::check(
            iv,
            (&ciphertext, &plaintext),
            &|iv| Cast5Cfb64Decryptor::new(&key, iv).unwrap(),
            Cast5Cfb64Decryptor::decrypt,
            Cast5Cfb64Decryptor::decrypt_final,
        );
    }
}

#[test]
fn errors() {
    assert_eq!(
        Cast5Cfb64Encryptor::new(&[], &[0; 8]).err(),
        Some(Error::InvalidKeyLength)
    );
    assert_eq!(
        Cast5Cfb64Decryptor::new(&[], &[0; 8]).err(),
        Some(Error::InvalidKeyLength)
    );
}
