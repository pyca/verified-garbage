//! SM4-GCM (`AeadTest` vectors, `sm4_gcm_test.json`).
//!
//! A valid vector must encrypt to exactly its ciphertext and tag, in place
//! and streaming (with the additional data and the text in two pieces each,
//! one of them split at every byte), and decrypt back, at once, streaming and with its
//! tag truncated. An invalid vector must be rejected, at once and streaming,
//! leaving the ciphertext as it was: by decryption (a modified tag,
//! ciphertext or additional data), or already by the nonce check (an empty
//! nonce). Its nonces are 1 to 257 bytes long; RFC 8998's example
//! (`tests/rfc8998/`) has a 12-byte one.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::sm4_gcm::{Error, Sm4Gcm};

use super::harness::{self, Count, Expectation};
use super::schema::{AeadCase, SizesGroup};
use crate::require_vectors;

/// The tag of `c`, which is 16 bytes long.
fn tag(c: &AeadCase) -> &[u8; 16] {
    c.tag.0.as_slice().try_into().unwrap()
}

/// Streaming decryption of `c` under `key`: the plaintext, if the tag
/// matched.
fn stream_decrypt(key: &Sm4Gcm, c: &AeadCase) -> Result<Vec<u8>, Error> {
    let mut d = key.decryptor(&c.iv.0)?;
    d.update_aad(&c.aad.0)?;
    let mut buf = c.ct.0.clone();
    d.update(&mut buf)?;
    d.finalize(tag(c))?;
    Ok(buf)
}

/// Decryption of `c` with its tag truncated to `N` bytes.
fn truncated<const N: usize>(key: &Sm4Gcm, c: &AeadCase) {
    let tag: &[u8; N] = c.tag.0[..N].try_into().unwrap();
    let mut buf = c.ct.0.clone();
    key.decrypt_in_place_truncated(&c.iv.0, &c.aad.0, &mut buf, tag)
        .unwrap();
    assert_eq!(buf, c.msg.0);
    let mut d = key.decryptor(&c.iv.0).unwrap();
    d.update_aad(&c.aad.0).unwrap();
    buf.copy_from_slice(&c.ct.0);
    d.update(&mut buf).unwrap();
    d.finalize_truncated(tag).unwrap();
    assert_eq!(buf, c.msg.0);
}

/// Streaming encryption of `c`, with the additional data split at `a` and
/// the text at `m`.
fn stream_encrypt(key: &Sm4Gcm, c: &AeadCase, a: usize, m: usize) -> (Vec<u8>, [u8; 16]) {
    let mut e = key.encryptor(&c.iv.0).unwrap();
    let (a0, a1) = c.aad.0.split_at(a);
    e.update_aad(a0).unwrap();
    e.update_aad(a1).unwrap();
    let mut buf = c.msg.0.clone();
    let (m0, m1) = buf.split_at_mut(m);
    e.update(m0).unwrap();
    e.update(m1).unwrap();
    let tag = e.finalize();
    (buf, tag)
}

#[test]
fn sm4_gcm() {
    require_vectors!();
    let file = harness::load::<SizesGroup, AeadCase>("sm4_gcm_test.json");
    let (valid, invalid) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        let c = &test.case;
        let id = test.tc_id;
        assert_eq!(group.params.tag_size, Some(8 * c.tag.0.len()), "tcId {id}");
        assert_eq!(group.params.tag_size, Some(128), "tcId {id}");
        let key = Sm4Gcm::new(c.key.0.as_slice().try_into().unwrap());
        let mut buf = c.ct.0.clone();
        let decrypted = key.decrypt_in_place(&c.iv.0, &c.aad.0, &mut buf, tag(c));
        match test.result {
            Expectation::Valid => {
                decrypted.unwrap_or_else(|e| panic!("tcId {id}: {e:?}"));
                assert_eq!(buf, c.msg.0, "tcId {id}");
                let mut buf = c.msg.0.clone();
                let sealed = key.encrypt_in_place(&c.iv.0, &c.aad.0, &mut buf);
                assert_eq!((buf, sealed), (c.ct.0.clone(), Ok(*tag(c))), "tcId {id}");
                let (a, m) = (c.aad.0.len(), c.msg.0.len());
                for (a, m) in (0..=a)
                    .map(|a| (a, m / 2))
                    .chain((0..=m).map(|m| (a / 2, m)))
                {
                    let sealed = stream_encrypt(&key, c, a, m);
                    assert_eq!(sealed, (c.ct.0.clone(), *tag(c)), "tcId {id}: {a}, {m}");
                }
                assert_eq!(stream_decrypt(&key, c), Ok(c.msg.0.clone()), "tcId {id}");
                truncated::<4>(&key, c);
                truncated::<8>(&key, c);
                truncated::<12>(&key, c);
                valid.add();
            }
            // The file has no acceptable vectors.
            _ => {
                assert!(matches!(test.result, Expectation::Invalid), "tcId {id}");
                assert!(decrypted.is_err(), "tcId {id}");
                assert!(stream_decrypt(&key, c).is_err(), "tcId {id}");
                assert_eq!(buf, c.ct.0, "tcId {id}: rejected ciphertext was modified");
                invalid.add();
            }
        }
    });
    assert!(valid.get() > 0 && invalid.get() > 0);
}
