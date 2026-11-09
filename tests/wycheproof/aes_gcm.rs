//! AES-GCM (`AeadTest` vectors, `aes_gcm_test.json`).
//!
//! A valid vector must encrypt to exactly its ciphertext and tag (in place,
//! and out of place from the plaintext whole and in two pieces), and decrypt
//! back, in place, out of place (with the input and the output at several
//! offsets) and streaming. An invalid vector must be rejected, at once, out
//! of place and streaming: by decryption (a modified tag, ciphertext or
//! additional data), which zeroes the output of an out-of-place decryption,
//! or already by the nonce check (an empty nonce), which leaves it as it was.
//!
//! Every vector has a full 16-byte tag; the CAVP vectors
//! (`tests/cavp/aes_gcm.rs`) test truncated ones.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use verified_garbage::aead::aes_gcm::{AesGcm, Error};

use super::harness::{self, Count, Expectation};
use super::schema::{AeadCase, SizesGroup};
use crate::require_vectors;

/// The tag of `c`, which is 16 bytes long.
fn tag(c: &AeadCase) -> &[u8; 16] {
    c.tag.0.as_slice().try_into().unwrap()
}

/// Streaming decryption of `c` under `key`: the plaintext, if the tag
/// matched.
fn stream_decrypt(key: &AesGcm, c: &AeadCase) -> Result<Vec<u8>, Error> {
    let mut d = key.decryptor(&c.iv.0)?;
    d.update_aad(&c.aad.0)?;
    let mut buf = c.ct.0.clone();
    d.update(&mut buf)?;
    d.finalize(tag(c))?;
    Ok(buf)
}

/// The offsets of the input and the output of out-of-place decryption: each
/// in a buffer of its own, at its start or not.
const OFFSETS: [(usize, usize); 5] = [(0, 0), (1, 3), (7, 0), (0, 15), (9, 9)];

/// Out-of-place decryption of `c` under `key`, with the ciphertext at offset
/// `so` of its buffer and the output at offset `doff` of one filled with
/// `0x55`: the result, and the output.
fn decrypt_at(key: &AesGcm, c: &AeadCase, so: usize, doff: usize) -> (Result<(), Error>, Vec<u8>) {
    let mut src = vec![0xaa; so + c.ct.0.len()];
    src[so..].copy_from_slice(&c.ct.0);
    let mut out = vec![0x55; doff + c.ct.0.len()];
    let r = key.decrypt(&c.iv.0, &c.aad.0, &src[so..], tag(c), &mut out[doff..]);
    assert!(out[..doff].iter().all(|&b| b == 0x55));
    (r, out[doff..].to_vec())
}

/// Check an extension length against the prefix of a published full tag.
fn truncated<const N: usize>(key: &AesGcm, c: &AeadCase) {
    let tag: &[u8; N] = c.tag.0[..N].try_into().unwrap();
    let mut out = vec![0; c.ct.0.len()];
    key.decrypt_truncated(&c.iv.0, &c.aad.0, &c.ct.0, tag, &mut out)
        .unwrap();
    assert_eq!(out, c.msg.0);
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

#[test]
fn aes_gcm() {
    require_vectors!();
    let file = harness::load::<SizesGroup, AeadCase>("aes_gcm_test.json");
    let (valid, invalid) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        let c = &test.case;
        let id = test.tc_id;
        assert_eq!(group.params.tag_size, Some(8 * c.tag.0.len()), "tcId {id}");
        assert_eq!(group.params.tag_size, Some(128), "tcId {id}");
        let key = AesGcm::new(&c.key.0).unwrap();
        let mut buf = c.ct.0.clone();
        let decrypted = key.decrypt_in_place(&c.iv.0, &c.aad.0, &mut buf, tag(c));
        match test.result {
            Expectation::Valid => {
                decrypted.unwrap_or_else(|e| panic!("tcId {id}: {e:?}"));
                assert_eq!(buf, c.msg.0, "tcId {id}");
                let mut buf = c.msg.0.clone();
                let tag = key.encrypt_in_place(&c.iv.0, &c.aad.0, &mut buf).unwrap();
                assert_eq!(buf, c.ct.0, "tcId {id}");
                assert_eq!(tag[..], c.tag.0, "tcId {id}");

                let mut e = key.encryptor(&c.iv.0).unwrap();
                e.update_aad(&c.aad.0).unwrap();
                let mut buf = c.msg.0.clone();
                e.update(&mut buf).unwrap();
                assert_eq!(buf, c.ct.0, "tcId {id}");
                assert_eq!(e.finalize(), tag, "tcId {id}");
                let (a, b) = c.msg.0.split_at(c.msg.0.len() / 3);
                for pieces in [&[&c.msg.0[..]][..], &[a, b]] {
                    let mut out = vec![0; c.msg.0.len()];
                    let sealed = key.encrypt(&c.iv.0, &c.aad.0, pieces, &mut out);
                    assert_eq!((out, sealed), (c.ct.0.clone(), Ok(tag)), "tcId {id}");
                }
                assert_eq!(stream_decrypt(&key, c), Ok(c.msg.0.clone()), "tcId {id}");
                for (so, doff) in OFFSETS {
                    assert_eq!(
                        decrypt_at(&key, c, so, doff),
                        (Ok(()), c.msg.0.clone()),
                        "tcId {id}"
                    );
                }
                // An output of another length than the ciphertext's.
                let mut out = vec![0x55; c.ct.0.len() + 1];
                let longer = key.decrypt(&c.iv.0, &c.aad.0, &c.ct.0, &tag, &mut out);
                assert_eq!(longer, Err(Error::InvalidOutputLength), "tcId {id}");
                if let Some(short) = out.get_mut(..c.ct.0.len().wrapping_sub(1)) {
                    let shorter = key.decrypt(&c.iv.0, &c.aad.0, &c.ct.0, &tag, short);
                    assert_eq!(shorter, Err(Error::InvalidOutputLength), "tcId {id}");
                }
                assert!(out.iter().all(|&b| b == 0x55), "tcId {id}");
                truncated::<5>(&key, c);
                truncated::<6>(&key, c);
                truncated::<7>(&key, c);
                truncated::<9>(&key, c);
                truncated::<10>(&key, c);
                truncated::<11>(&key, c);
                valid.add();
            }
            // The file has no acceptable vectors.
            _ => {
                assert!(matches!(test.result, Expectation::Invalid), "tcId {id}");
                assert!(decrypted.is_err(), "tcId {id}");
                assert!(stream_decrypt(&key, c).is_err(), "tcId {id}");
                assert_eq!(buf, c.ct.0, "tcId {id}: rejected ciphertext was modified");
                for (so, doff) in OFFSETS {
                    let (r, out) = decrypt_at(&key, c, so, doff);
                    // A wrong tag zeroes the output; an invalid nonce leaves it.
                    let fill = if r == Err(Error::TagMismatch) {
                        0
                    } else {
                        0x55
                    };
                    assert!(r.is_err(), "tcId {id}");
                    assert!(out.iter().all(|&b| b == fill), "tcId {id}: {r:?}");
                }
                invalid.add();
            }
        }
    });
    assert!(valid.get() > 0 && invalid.get() > 0);
}
