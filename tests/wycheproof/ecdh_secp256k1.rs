//! Wycheproof's secp256k1 WebCrypto vectors. JWK coordinates are converted
//! to the uncompressed SEC 1 encoding accepted by the public API.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use serde::Deserialize;
use verified_garbage::ecdh::{Error, PrivateKey, Secp256k1};

use super::harness::{self, Count, Expectation, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
struct Group {
    curve: String,
}

#[derive(Deserialize)]
struct Public {
    crv: String,
    x: String,
    y: String,
}

#[derive(Deserialize)]
struct Private {
    d: String,
    #[serde(flatten)]
    public: Public,
}

#[derive(Deserialize)]
struct Case {
    public: Public,
    private: Private,
    shared: Hex,
}

// The published JWK strings use unpadded base64url.
fn decode(s: &str) -> Vec<u8> {
    let alphabet = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    s.as_bytes()
        .chunks(4)
        .flat_map(|chunk| {
            let word = chunk.iter().enumerate().fold(0u32, |word, (i, c)| {
                word | ((alphabet.iter().position(|a| a == c).unwrap() as u32) << (18 - 6 * i))
            });
            word.to_be_bytes()[1..chunk.len()].to_vec()
        })
        .collect()
}

fn public(key: &Public) -> Vec<u8> {
    [vec![4], decode(&key.x), decode(&key.y)].concat()
}

#[test]
fn ecdh_secp256k1_webcrypto_test() {
    require_vectors!();
    let file = harness::load::<Group, Case>("ecdh_secp256k1_webcrypto_test.json");
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
