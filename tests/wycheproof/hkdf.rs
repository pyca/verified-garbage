//! HKDF-SHA-1, HKDF-SHA-256, HKDF-SHA-384 and HKDF-SHA-512 (`HkdfTest`
//! vectors).

#![cfg(any(target_arch = "riscv64", target_arch = "x86_64"))]

use verified_garbage::hashes::sha1::Sha1;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hashes::sha512::Sha512;
use verified_garbage::kdf::hkdf::{Hkdf, HkdfHash, OutputTooLong};

use super::harness::{self, Expectation, Fields, Hex};
use crate::{json_struct, require_vectors};

json_struct! {
    struct Case {
        ikm: Hex,
        salt: Hex,
        info: Hex,
        size: usize,
        okm: Hex,
    }
}

/// Checks every vector of `name` with HKDF over `H`: a valid one's output
/// keying material is derived, from a salt given or not (the files' empty
/// salts), and from the pseudorandom key extracted (`from_prk`); each of its
/// prefixes at the lengths around the blocks' ends is the material derived at
/// that length (HKDF-Expand's output at a shorter length is a prefix of its
/// output at a longer one), into a buffer at an odd address too; and an
/// invalid one (too long) is rejected, with the buffer unchanged.
fn check<H: HkdfHash>(name: &str) {
    let file = harness::load::<Fields, Case>(name);
    file.par_tests(|_, test| {
        let c = &test.case;
        let salts: &[Option<&[u8]>] = if c.salt.0.is_empty() {
            &[None, Some(&[])]
        } else {
            &[Some(&c.salt.0)]
        };
        for &salt in salts {
            let mut okm = vec![0x5a; c.size];
            let hkdf = Hkdf::<H>::new(salt, &c.ikm.0);
            let r = hkdf.expand(&c.info.0, &mut okm);
            match test.result {
                Expectation::Valid => {
                    assert_eq!(r, Ok(()), "tcId {}", test.tc_id);
                    assert_eq!(okm, c.okm.0, "tcId {}", test.tc_id);
                }
                _ => {
                    assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
                    assert_eq!(r, Err(OutputTooLong), "tcId {}", test.tc_id);
                    assert!(okm.iter().all(|&b| b == 0x5a), "tcId {}", test.tc_id);
                    continue;
                }
            }
            let (prk, from_new) = Hkdf::<H>::extract(salt, &c.ikm.0);
            assert_eq!(prk.as_ref().len(), H::OUTPUT_SIZE);
            let d = H::OUTPUT_SIZE;
            for hkdf in [from_new, Hkdf::<H>::from_prk(prk.as_ref()).unwrap()] {
                for len in [0, 1, d - 1, d, d + 1, 2 * d, c.size - 1, c.size] {
                    if len > c.size {
                        continue;
                    }
                    let mut buf = vec![0; len + 1];
                    hkdf.expand(&c.info.0, &mut buf[1..]).unwrap();
                    assert_eq!(buf[1..], c.okm.0[..len], "tcId {} at {len}", test.tc_id);
                }
            }
        }
    });
}

#[test]
fn hkdf_sha1() {
    require_vectors!();
    check::<Sha1>("hkdf_sha1_test.json");
}

#[test]
fn hkdf_sha256() {
    require_vectors!();
    check::<Sha256>("hkdf_sha256_test.json");
}

#[test]
fn hkdf_sha384() {
    require_vectors!();
    check::<Sha384>("hkdf_sha384_test.json");
}

#[test]
fn hkdf_sha512() {
    require_vectors!();
    check::<Sha512>("hkdf_sha512_test.json");
}

/// `from_prk` rejects a pseudorandom key shorter than a digest, and takes
/// one of a digest or longer.
#[test]
fn hkdf_from_prk_lengths() {
    use verified_garbage::error::InvalidKeyLength;
    assert_eq!(
        Hkdf::<Sha256>::from_prk(&[0; 31]).unwrap_err(),
        InvalidKeyLength
    );
    assert!(Hkdf::<Sha256>::from_prk(&[0; 32]).is_ok());
    assert!(Hkdf::<Sha256>::from_prk(&[0; 200]).is_ok());
    assert_eq!(
        Hkdf::<Sha512>::from_prk(&[0; 63]).unwrap_err(),
        InvalidKeyLength
    );
}
