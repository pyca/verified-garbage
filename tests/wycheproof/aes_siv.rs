//! AES-SIV (`DaeadTest` vectors, `aes_siv_cmac_test.json`, and `AeadTest`
//! vectors, `aead_aes_siv_cmac_test.json`).
//!
//! The deterministic vectors have one associated-data component, and their
//! ciphertext is the synthetic IV followed by the encrypted data. The AEAD
//! vectors use RFC 5297 §3's nonce-based form: the components are the
//! associated data, then the nonce. A valid vector must encrypt to exactly
//! its ciphertext and IV, and decrypt back; an invalid one (a modified IV)
//! must be rejected, with the data overwritten by zeros.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use serde::Deserialize;
use verified_garbage::aes_siv::{AesSiv, Error};

use super::harness::{self, Count, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct DaeadGroup {
    key_size: usize,
}

#[derive(Deserialize)]
struct DaeadCase {
    key: Hex,
    aad: Hex,
    msg: Hex,
    ct: Hex,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct AeadGroup {
    key_size: usize,
    tag_size: usize,
}

#[derive(Deserialize)]
struct AeadCase {
    key: Hex,
    iv: Hex,
    aad: Hex,
    msg: Hex,
    ct: Hex,
    tag: Hex,
}

/// Checks one vector: the key, the components, the plaintext, the
/// synthetic IV and the encrypted data.
fn check(
    id: u64,
    result: Expectation,
    key: &[u8],
    ads: &[&[u8]],
    msg: &[u8],
    tag: &[u8],
    ct: &[u8],
) {
    let key = AesSiv::new(key).unwrap();
    let tag: &[u8; 16] = tag.try_into().unwrap();
    let mut buf = ct.to_vec();
    let decrypted = key.decrypt_in_place(ads, &mut buf, tag);
    if result == Expectation::Valid {
        assert_eq!(decrypted, Ok(()), "tcId {id}");
        assert_eq!(buf, msg, "tcId {id}");
        let mut buf = msg.to_vec();
        let v = key.encrypt_in_place(ads, &mut buf).unwrap();
        assert_eq!(buf, ct, "tcId {id}");
        assert_eq!(&v, tag, "tcId {id}");
    } else {
        assert_eq!(result, Expectation::Invalid, "tcId {id}");
        assert_eq!(decrypted, Err(Error::TagMismatch), "tcId {id}");
        assert!(buf.iter().all(|&b| b == 0), "tcId {id}");
    }
}

#[test]
fn aes_siv_cmac() {
    require_vectors!();
    let file = harness::load::<DaeadGroup, DaeadCase>("aes_siv_cmac_test.json");
    let (valid, invalid) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        let c = &test.case;
        let id = test.tc_id;
        assert_eq!(group.params.key_size, 8 * c.key.0.len(), "tcId {id}");
        let (tag, ct) = c.ct.0.split_at(16);
        check(id, test.result, &c.key.0, &[&c.aad.0], &c.msg.0, tag, ct);
        if test.result == Expectation::Valid {
            valid.add();
        } else {
            invalid.add();
        }
    });
    assert!(valid.get() > 0 && invalid.get() > 0);
}

#[test]
fn aead_aes_siv_cmac() {
    require_vectors!();
    let file = harness::load::<AeadGroup, AeadCase>("aead_aes_siv_cmac_test.json");
    let (valid, invalid) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        let c = &test.case;
        let id = test.tc_id;
        assert_eq!(group.params.key_size, 8 * c.key.0.len(), "tcId {id}");
        assert_eq!(group.params.tag_size, 128, "tcId {id}");
        check(
            id,
            test.result,
            &c.key.0,
            &[&c.aad.0, &c.iv.0],
            &c.msg.0,
            &c.tag.0,
            &c.ct.0,
        );
        if test.result == Expectation::Valid {
            valid.add();
        } else {
            invalid.add();
        }
    });
    assert!(valid.get() > 0 && invalid.get() > 0);
}
