//! SEC 1 conversions of the public keys in Wycheproof's ECDSA groups,
//! plus its compressed ECDH encodings, including malformed coordinates.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use serde::Deserialize;
use verified_garbage::ecdh::{
    BrainpoolP256r1, BrainpoolP384r1, BrainpoolP512r1, P192, P224, P256, P384, P521, PrivateKey,
    Secp256k1,
};

use super::harness::{self, Count, Expectation, Fields, Hex};
use crate::require_vectors;

#[derive(Deserialize)]
struct Key {
    uncompressed: Hex,
}

#[derive(Deserialize)]
struct EcdsaGroup {
    #[serde(rename = "publicKey")]
    public_key: Key,
}

macro_rules! public_keys {
    ($test:ident, $curve:ident, $len:literal, $file:literal) => {
        #[test]
        fn $test() {
            require_vectors!();
            let file = harness::load::<EcdsaGroup, Fields>($file);
            assert!(!file.test_groups.is_empty());
            harness::par_each(&file.test_groups, |g| {
                let public: [u8; 2 * $len + 1] =
                    g.params.public_key.uncompressed.0[..].try_into().unwrap();
                // The reference encoding follows SEC 1 §2.3.3 directly
                // from the published uncompressed point's x and y bytes.
                let mut expected = [0; $len + 1];
                expected[0] = 2 | (public[2 * $len] & 1);
                expected[1..].copy_from_slice(&public[1..1 + $len]);
                assert_eq!($curve::compress_public_key(&public), Some(expected));
                assert_eq!($curve::decompress_public_key(&expected), Some(public));
            });
        }
    };
}

public_keys!(p192, P192, 24, "ecdsa_secp192r1_sha256_p1363_test.json");
public_keys!(p224, P224, 28, "ecdsa_secp224r1_sha224_p1363_test.json");
public_keys!(p256, P256, 32, "ecdsa_secp256r1_sha256_p1363_test.json");
public_keys!(p384, P384, 48, "ecdsa_secp384r1_sha384_p1363_test.json");
public_keys!(p521, P521, 66, "ecdsa_secp521r1_sha512_p1363_test.json");
public_keys!(
    secp256k1,
    Secp256k1,
    32,
    "ecdsa_secp256k1_sha256_p1363_test.json"
);
public_keys!(
    brainpoolp256r1,
    BrainpoolP256r1,
    32,
    "ecdsa_brainpoolP256r1_sha256_p1363_test.json"
);
public_keys!(
    brainpoolp384r1,
    BrainpoolP384r1,
    48,
    "ecdsa_brainpoolP384r1_sha384_p1363_test.json"
);
public_keys!(
    brainpoolp512r1,
    BrainpoolP512r1,
    64,
    "ecdsa_brainpoolP512r1_sha512_p1363_test.json"
);

#[derive(Deserialize)]
struct EcdhCase {
    public: Hex,
    private: Hex,
    shared: Hex,
}

macro_rules! compressed_peers {
    ($test:ident, $curve:ident, $len:literal, $file:literal) => {
        #[test]
        fn $test() {
            require_vectors!();
            let file = harness::load::<Fields, EcdhCase>($file);
            let (checked, rejected) = (Count::default(), Count::default());
            file.par_tests(|_, test| {
                let Ok(compressed) = <[u8; $len + 1]>::try_from(&test.case.public.0[..]) else {
                    return;
                };
                let public = $curve::decompress_public_key(&compressed);
                if let Some(public) = public {
                    assert_ne!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
                    assert_eq!($curve::compress_public_key(&public), Some(compressed));
                    let bytes = test
                        .case
                        .private
                        .0
                        .strip_prefix(&[0])
                        .unwrap_or(&test.case.private.0);
                    let mut private = [0; $len];
                    private[$len - bytes.len()..].copy_from_slice(bytes);
                    let key = PrivateKey::<$curve>::from_bytes(&private);
                    let shared = key.diffie_hellman(&public).unwrap().to_vec();
                    assert_eq!(shared, test.case.shared.0, "tcId {}", test.tc_id);
                    checked.add();
                } else {
                    assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
                    rejected.add();
                }
            });
            assert!(checked.get() > 0 && rejected.get() > 0);
        }
    };
}

compressed_peers!(p224_peers, P224, 28, "ecdh_secp224r1_ecpoint_test.json");
compressed_peers!(p256_peers, P256, 32, "ecdh_secp256r1_ecpoint_test.json");
compressed_peers!(p384_peers, P384, 48, "ecdh_secp384r1_ecpoint_test.json");
compressed_peers!(p521_peers, P521, 66, "ecdh_secp521r1_ecpoint_test.json");
