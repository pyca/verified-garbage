//! IDEA-CFB64: pyca/cryptography's vectors (derived from the AESVS MMT
//! data, verified against Botan), unmodified under vectors/, truncated and
//! split (`tests/modes.rs`).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::idea_cfb::{Error, IdeaCfb64Decryptor, IdeaCfb64Encryptor};

use verified_garbage_test_vectors::unhex;

#[test]
fn pyca_vectors() {
    let text = crate::vectors::text("vectors/cryptography-idea-cfb/idea-cfb.txt");
    let mut key_lens = Vec::new();
    for record in text.split("COUNT = ").skip(1) {
        let get = |label: &str| {
            let line = record.lines().find(|l| l.starts_with(label)).unwrap();
            unhex(line.split_once(" = ").unwrap().1.trim())
        };
        let key = get("KEY");
        let iv: [u8; 8] = get("IV").try_into().unwrap();
        let (plaintext, ciphertext) = (get("PLAINTEXT"), get("CIPHERTEXT"));
        key_lens.push(key.len());
        let vector = (&plaintext[..], &ciphertext[..]);
        crate::modes::check(
            iv,
            vector,
            &|iv| IdeaCfb64Encryptor::new(&key, iv).unwrap(),
            IdeaCfb64Encryptor::encrypt,
            IdeaCfb64Encryptor::encrypt_final,
        );
        crate::modes::check(
            iv,
            (&ciphertext, &plaintext),
            &|iv| IdeaCfb64Decryptor::new(&key, iv).unwrap(),
            IdeaCfb64Decryptor::decrypt,
            IdeaCfb64Decryptor::decrypt_final,
        );
    }
    assert_eq!(key_lens, [16; 20]);
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 24, 32] {
        assert_eq!(
            IdeaCfb64Encryptor::new(&vec![0; len], &[0; 8]).err(),
            Some(Error::InvalidKeyLength)
        );
        assert_eq!(
            IdeaCfb64Decryptor::new(&vec![0; len], &[0; 8]).err(),
            Some(Error::InvalidKeyLength)
        );
    }
}
