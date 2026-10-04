//! AES-CCM (`AeadTest` vectors, `aes_ccm_test.json`).
//!
//! A valid vector must encrypt to exactly its ciphertext and tag, and
//! decrypt back. An invalid vector must be rejected: by decryption (a
//! modified tag), by the nonce check (a nonce shorter than 7 or longer than
//! 13 bytes), or, for a tag length Appendix A.1 does not allow, already by
//! the type of the tag, which cannot be written.

#![cfg(target_arch = "x86_64")]

use serde::Deserialize;
use verified_garbage::aes_ccm::{AesCcm, Error};

use crate::harness::{self, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Group {
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

/// Decrypts `c` under `key` with a `T`-byte tag, leaving the result in
/// `buf`; for a valid vector, also encrypts and checks the ciphertext and
/// tag.
fn check<const T: usize>(key: &AesCcm, c: &Case, buf: &mut [u8], valid: bool) -> Result<(), Error> {
    let tag: &[u8; T] = c.tag.0.as_slice().try_into().unwrap();
    let r = key.decrypt_in_place(&c.iv.0, &c.aad.0, buf, tag);
    if valid {
        let mut e = c.msg.0.clone();
        let t = key
            .encrypt_in_place::<T>(&c.iv.0, &c.aad.0, &mut e)
            .unwrap();
        assert_eq!(e, c.ct.0);
        assert_eq!(t[..], c.tag.0);
    }
    r
}

#[test]
fn aes_ccm() {
    require_vectors!();
    let file = harness::load::<Group, Case>("aes_ccm_test.json");
    let (mut valid, mut invalid) = (0, 0);
    for (group, test) in file.tests() {
        let c = &test.case;
        let id = test.tc_id;
        assert_eq!(group.params.tag_size, 8 * c.tag.0.len(), "tcId {id}");
        let key = AesCcm::new(&c.key.0).unwrap();
        let ok = matches!(test.result, Expectation::Valid);
        let mut buf = c.ct.0.clone();
        let decrypted = match c.tag.0.len() {
            4 => check::<4>(&key, c, &mut buf, ok),
            6 => check::<6>(&key, c, &mut buf, ok),
            8 => check::<8>(&key, c, &mut buf, ok),
            10 => check::<10>(&key, c, &mut buf, ok),
            12 => check::<12>(&key, c, &mut buf, ok),
            14 => check::<14>(&key, c, &mut buf, ok),
            16 => check::<16>(&key, c, &mut buf, ok),
            // No tag of this length can be passed.
            _ => {
                assert!(matches!(test.result, Expectation::Invalid), "tcId {id}");
                invalid += 1;
                continue;
            }
        };
        match test.result {
            Expectation::Valid => {
                decrypted.unwrap_or_else(|e| panic!("tcId {id}: {e:?}"));
                assert_eq!(buf, c.msg.0, "tcId {id}");
                valid += 1;
            }
            // The file has no acceptable vectors.
            _ => {
                assert!(matches!(test.result, Expectation::Invalid), "tcId {id}");
                if decrypted == Err(Error::TagMismatch) {
                    assert!(buf.iter().all(|&b| b == 0), "tcId {id}");
                } else {
                    assert_eq!(decrypted, Err(Error::InvalidNonceLength), "tcId {id}");
                    assert_eq!(buf, c.ct.0, "tcId {id}");
                }
                invalid += 1;
            }
        }
    }
    assert!(valid > 0 && invalid > 0);
}
