//! AES-GCM: every vector of the GCM files (read at run time: they are 17
//! MB), encryption with an external IV and decryption, for 128-, 192- and
//! 256-bit keys.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::aes_gcm::{AesGcm, Error};

use verified_garbage_test_vectors::{Record, cavp_blocks};

use super::unhex;

/// The records of a GCM response file, from each `Count` line to the next
/// blank line, and whether each has a bare `FAIL` line, its only line that
/// is not a field.
fn records(text: &str) -> Vec<(Record<'_>, bool)> {
    let mut records = Vec::new();
    for (fields, bare) in cavp_blocks(text, "Count") {
        let fail = bare == ["FAIL"];
        assert!(fail || bare.is_empty(), "not a field: {bare:?}");
        records.push((fields, fail));
    }
    records
}

/// Decrypts `data` with `tag`, whose length the vector gives: the API takes
/// it as a type parameter, so each length §5.2.1.2 allows is a separate call.
fn decrypt(key: &AesGcm, iv: &[u8], aad: &[u8], data: &mut [u8], tag: &[u8]) -> Result<(), Error> {
    match tag.len() {
        4 => key.decrypt_in_place_truncated::<4>(iv, aad, data, tag.try_into().unwrap()),
        8 => key.decrypt_in_place_truncated::<8>(iv, aad, data, tag.try_into().unwrap()),
        12 => key.decrypt_in_place_truncated::<12>(iv, aad, data, tag.try_into().unwrap()),
        13 => key.decrypt_in_place_truncated::<13>(iv, aad, data, tag.try_into().unwrap()),
        14 => key.decrypt_in_place_truncated::<14>(iv, aad, data, tag.try_into().unwrap()),
        15 => key.decrypt_in_place_truncated::<15>(iv, aad, data, tag.try_into().unwrap()),
        // Panics on any other length.
        _ => key.decrypt_in_place(iv, aad, data, tag.try_into().unwrap()),
    }
}

/// Encryption with an external IV must give the ciphertext and the tag
/// (truncated to its length), and decryption must return the plaintext or,
/// for a `FAIL` vector, reject the tag.
#[test]
fn aes_gcm() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("vectors/nist-cavp/gcm");
    let (mut encrypted, mut decrypted, mut failed) = (0, 0, 0);
    for bits in [128, 192, 256] {
        let text = std::fs::read_to_string(dir.join(format!("gcmEncryptExtIV{bits}.rsp"))).unwrap();
        for (r, fail) in records(&text) {
            assert!(!fail);
            let key = AesGcm::new(&unhex(r["Key"])).unwrap();
            let tag = unhex(r["Tag"]);
            let mut buf = unhex(r["PT"]);
            let t = key
                .encrypt_in_place(&unhex(r["IV"]), &unhex(r["AAD"]), &mut buf)
                .unwrap();
            assert_eq!(buf, unhex(r["CT"]));
            assert_eq!(t[..tag.len()], tag);
            encrypted += 1;
        }
        let text = std::fs::read_to_string(dir.join(format!("gcmDecrypt{bits}.rsp"))).unwrap();
        for (r, fail) in records(&text) {
            let key = AesGcm::new(&unhex(r["Key"])).unwrap();
            let mut buf = unhex(r["CT"]);
            let tag = unhex(r["Tag"]);
            let result = decrypt(&key, &unhex(r["IV"]), &unhex(r["AAD"]), &mut buf, &tag);
            if fail {
                assert!(result.is_err());
                failed += 1;
            } else {
                result.unwrap();
                assert_eq!(buf, unhex(r["PT"]));
            }
            decrypted += 1;
        }
    }
    assert_eq!((encrypted, decrypted), (3 * 7875, 3 * 7875));
    assert!(0 < failed && failed < decrypted);
}
