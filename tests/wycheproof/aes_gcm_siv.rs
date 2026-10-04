//! AES-GCM-SIV (`AeadTest` vectors, `aes_gcm_siv_test.json`).
//!
//! A valid vector must encrypt to exactly its ciphertext and tag, and
//! decrypt back. An invalid vector (a modified tag) must be rejected by
//! decryption, which leaves zeros.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use serde::Deserialize;
use verified_garbage::aes_gcm_siv::{AesGcmSiv, Error};

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
    iv_size: usize,
    tag_size: usize,
}

#[derive(Deserialize)]
struct Case {
    key: Hex,
    iv: Hex,
    aad: Hex,
    msg: Hex,
    ct: Hex,
    tag: Hex,
}

#[test]
fn aes_gcm_siv() {
    require_vectors!();
    let file = harness::load::<Group, Case>("aes_gcm_siv_test.json");
    let (mut valid, mut invalid) = (0, 0);
    for (group, test) in file.tests() {
        let c = &test.case;
        let id = test.tc_id;
        let sizes = (group.params.iv_size, group.params.tag_size);
        assert_eq!(sizes, (96, 128), "tcId {id}");
        let key = AesGcmSiv::new(&c.key.0).unwrap();
        let nonce: &[u8; 12] = c.iv.0.as_slice().try_into().unwrap();
        let tag: &[u8; 16] = c.tag.0.as_slice().try_into().unwrap();
        let mut buf = c.ct.0.clone();
        let decrypted = key.decrypt_in_place(nonce, &c.aad.0, &mut buf, tag);
        match test.result {
            Expectation::Valid => {
                decrypted.unwrap_or_else(|e| panic!("tcId {id}: {e:?}"));
                assert_eq!(buf, c.msg.0, "tcId {id}");
                let mut e = c.msg.0.clone();
                let t = key.encrypt_in_place(nonce, &c.aad.0, &mut e).unwrap();
                assert_eq!(e, c.ct.0, "tcId {id}");
                assert_eq!(t[..], c.tag.0, "tcId {id}");
                valid += 1;
            }
            // The file has no acceptable vectors.
            _ => {
                assert!(matches!(test.result, Expectation::Invalid), "tcId {id}");
                assert_eq!(decrypted, Err(Error::TagMismatch), "tcId {id}");
                assert!(buf.iter().all(|&b| b == 0), "tcId {id}");
                invalid += 1;
            }
        }
    }
    assert!(valid > 0 && invalid > 0);
}
