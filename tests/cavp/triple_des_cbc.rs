//! Triple DES-CBC: NIST CAVP's multi-block message tests, unmodified under
//! vectors/, whole and split at every block.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::error::{IncompleteBlock, InvalidKeyLength};

use verified_garbage::triple_des_cbc::{TripleDesCbcDecryptor, TripleDesCbcEncryptor};

use verified_garbage_test_vectors::{cavp_records, unhex};

/// `plaintext` encrypts to `ciphertext` and decrypts back, whole and split
/// at every block boundary.
fn check(key: &[u8], iv: [u8; 8], plaintext: &[u8], ciphertext: &[u8]) {
    for offset in (0..=plaintext.len()).step_by(8) {
        let mut buffer = plaintext.to_vec();
        let mut encryptor = TripleDesCbcEncryptor::new(key, &iv).unwrap();
        encryptor.encrypt(&mut buffer[..offset]).unwrap();
        encryptor.encrypt(&mut buffer[offset..]).unwrap();
        assert_eq!(buffer, ciphertext);
        let mut decryptor = TripleDesCbcDecryptor::new(key, &iv).unwrap();
        decryptor.decrypt(&mut buffer[..offset]).unwrap();
        decryptor.decrypt(&mut buffer[offset..]).unwrap();
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
            "vectors/nist-cavp-tdes-mmt/TCBCMMT2.rsp"
        )),
        10
    );
    assert_eq!(
        check_file(&crate::vectors::text(
            "vectors/nist-cavp-tdes-mmt/TCBCMMT3.rsp"
        )),
        20
    );
}

#[test]
fn errors() {
    for len in [0, 8, 15, 17, 32] {
        assert!(matches!(
            TripleDesCbcEncryptor::new(&vec![0; len], &[0; 8]),
            Err(InvalidKeyLength)
        ));
        assert!(matches!(
            TripleDesCbcDecryptor::new(&vec![0; len], &[0; 8]),
            Err(InvalidKeyLength)
        ));
    }
    let key = [0; 24];
    let mut encryptor = TripleDesCbcEncryptor::new(&key, &[7; 8]).unwrap();
    let mut decryptor = TripleDesCbcDecryptor::new(&key, &[7; 8]).unwrap();
    for len in [1, 7, 9, 15] {
        let mut buffer = vec![0x5a; len];
        assert_eq!(encryptor.encrypt(&mut buffer), Err(IncompleteBlock));
        assert_eq!(decryptor.decrypt(&mut buffer), Err(IncompleteBlock));
        assert_eq!(buffer, vec![0x5a; len]);
    }
    // The failed calls changed nothing.
    let mut buffer = [0x5a; 16];
    let mut expected = buffer;
    TripleDesCbcEncryptor::new(&key, &[7; 8])
        .unwrap()
        .encrypt(&mut expected)
        .unwrap();
    encryptor.encrypt(&mut buffer).unwrap();
    assert_eq!(buffer, expected);
    decryptor.decrypt(&mut buffer).unwrap();
    assert_eq!(buffer, [0x5a; 16]);
}
