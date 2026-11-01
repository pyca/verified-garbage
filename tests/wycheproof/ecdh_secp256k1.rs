//! Wycheproof's secp256k1 WebCrypto vectors. JWK coordinates are converted
//! to the uncompressed SEC 1 encoding accepted by the public API.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use crate::json_struct;
use verified_garbage::ecdh::{Error, PrivateKey, Secp256k1};

use super::harness::{self, Count, Expectation, Hex};
use super::schema::CurveGroup;
use crate::require_vectors;

json_struct! {
    struct Public {
        crv: String,
        x: String,
        y: String,
    }
}

json_struct! {
    struct Private {
        d: String,
        #[json(flatten)]
        public: Public,
    }
}

json_struct! {
    struct Case {
        public: Public,
        private: Private,
        shared: Hex,
    }
}

// The published JWK strings use unpadded base64url.
fn decode(s: &str) -> Vec<u8> {
    let alphabet = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    let mut out = Vec::new();
    for chunk in s.as_bytes().chunks(4) {
        let word = chunk.iter().enumerate().fold(0u32, |word, (i, c)| {
            word | ((alphabet.iter().position(|a| a == c).unwrap() as u32) << (18 - 6 * i))
        });
        out.extend_from_slice(&word.to_be_bytes()[1..chunk.len()]);
    }
    out
}

fn public(key: &Public) -> Vec<u8> {
    [vec![4], decode(&key.x), decode(&key.y)].concat()
}

#[test]
fn ecdh_secp256k1_webcrypto_test() {
    require_vectors!();
    let file = harness::load::<CurveGroup, Case>("ecdh_secp256k1_webcrypto_test.json");
    let (checked, refused) = (Count::default(), Count::default());
    file.par_tests(|group, test| {
        assert_eq!(group.params.curve, "P-256K");
        let d = decode(&test.case.private.d).try_into().unwrap();
        let key = PrivateKey::<Secp256k1>::from_bytes(&d);
        // A key tagged with another curve cannot be represented by this
        // curve-specific API, even if its coordinates also lie on secp256k1.
        if test.case.public.crv != group.params.curve {
            assert_eq!(test.result, Expectation::Invalid);
            return;
        }
        let peer = public(&test.case.public).try_into().unwrap();
        #[cfg(target_arch = "x86_64")]
        {
            let mut one = [0; 32];
            one[31] = 1;
            let reference = PrivateKey::<Secp256k1>::from_bytes(&one);
            let valid = Secp256k1::validate_public_key(&peer);
            let expected = reference.diffie_hellman(&peer).is_ok();
            assert_eq!(valid, expected, "point check, tcId {}", test.tc_id);
        }
        let result = key.diffie_hellman(&peer);
        match test.result {
            Expectation::Valid => {
                let shared = result.map(|z| z.to_vec());
                let expected = Ok(test.case.shared.0.clone());
                assert_eq!(shared, expected, "tcId {}", test.tc_id);
                assert_eq!(
                    key.public_key().unwrap().as_slice(),
                    public(&test.case.private.public)
                );
                checked.add();
            }
            Expectation::Invalid | Expectation::Acceptable => {
                assert_eq!(result, Err(Error::InvalidKey), "tcId {}", test.tc_id);
                refused.add();
            }
        }
    });
    assert!(checked.get() > 0 && refused.get() > 0);
}

/// 0 and 2²⁵⁶ − 1 (above n) are not in [1, n − 1].
#[test]
fn secp256k1_private_keys_out_of_range() {
    for d in [[0; 32], [0xff; 32]] {
        assert_eq!(
            PrivateKey::<Secp256k1>::from_bytes(&d).public_key(),
            Err(Error::InvalidKey)
        );
    }
}
