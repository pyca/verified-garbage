//! Triple DES-CFB64: NIST CAVP's multi-block message tests, unmodified under
//! vectors/, truncated and split (`tests/modes.rs`), for each key length.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::error::InvalidKeyLength;

use verified_garbage::cipher::triple_des::{TripleDesCfb64Decryptor, TripleDesCfb64Encryptor};

use verified_garbage_test_vectors::{cavp_records, unhex};

/// `plaintext` encrypts to `ciphertext` and decrypts back, truncated and
/// split (`crate::modes::check`).
fn check(key: &[u8], iv: [u8; 8], plaintext: &[u8], ciphertext: &[u8]) {
    let vector = (plaintext, ciphertext);
    crate::modes::check(
        iv,
        vector,
        &|iv| TripleDesCfb64Encryptor::new(key, iv).unwrap(),
        TripleDesCfb64Encryptor::encrypt,
        TripleDesCfb64Encryptor::encrypt_final,
    );
    crate::modes::check(
        iv,
        (ciphertext, plaintext),
        &|iv| TripleDesCfb64Decryptor::new(key, iv).unwrap(),
        TripleDesCfb64Decryptor::decrypt,
        TripleDesCfb64Decryptor::decrypt_final,
    );
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
            "vectors/nist-cavp-tdes-mmt/TCFB64MMT2.rsp"
        )),
        10
    );
    assert_eq!(
        check_file(&crate::vectors::text(
            "vectors/nist-cavp-tdes-mmt/TCFB64MMT3.rsp"
        )),
        20
    );
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 32] {
        assert_eq!(
            TripleDesCfb64Encryptor::new(&vec![0; len], &[0; 8]).err(),
            Some(InvalidKeyLength)
        );
        assert_eq!(
            TripleDesCfb64Decryptor::new(&vec![0; len], &[0; 8]).err(),
            Some(InvalidKeyLength)
        );
    }
}

/// Messages of many of decryption's groups of blocks (256 on x86-64), from
/// the last CAVP vector's plaintext repeated: decryption undoes encryption,
/// whole and in pieces of sizes around the groups'.
#[test]
fn long_messages() {
    let text = crate::vectors::text("vectors/nist-cavp-tdes-mmt/TCFB64MMT3.rsp");
    let records = cavp_records(&text);
    let fields = records.last().unwrap();
    let mut key = unhex(fields["KEY1"]);
    key.extend(unhex(fields["KEY2"]));
    key.extend(unhex(fields["KEY3"]));
    let iv: [u8; 8] = unhex(fields["IV"]).try_into().unwrap();
    let block = unhex(fields["PLAINTEXT"]);
    let plaintext: Vec<u8> = block.iter().copied().cycle().take(8 * 1000).collect();
    let mut ciphertext = plaintext.clone();
    TripleDesCfb64Encryptor::new(&key, &iv)
        .unwrap()
        .encrypt(&mut ciphertext)
        .unwrap();
    for piece in [1000, 1, 255, 256, 257, 511, 512, 513] {
        let mut buffer = ciphertext.clone();
        let mut decryptor = TripleDesCfb64Decryptor::new(&key, &iv).unwrap();
        for chunk in buffer.chunks_mut(8 * piece) {
            decryptor.decrypt(chunk).unwrap();
        }
        assert_eq!(buffer, plaintext, "{piece}");
    }
}
