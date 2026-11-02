//! SEC 1 conversions: the public keys of Wycheproof's ECDSA groups,
//! compressed and back, and its compressed ECDH encodings, including
//! malformed coordinates, decompressed, compressed back and used: a file per
//! curve, each on the architectures of its curve.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::json_struct;

use super::harness::Hex;
use crate::wycheproof::schema::EcdhCase;

json_struct! {
    pub(super) struct Key {
        uncompressed: Hex,
    }
}

json_struct! {
    pub(super) struct EcdsaGroup {
        #[json(rename = "publicKey")]
        public_key: Key,
    }
}

macro_rules! public_keys {
    ($test:ident, $curve:ident, $len:literal, $file:literal) => {
        #[test]
        fn $test() {
            crate::require_vectors!();
            let file = crate::wycheproof::harness::load::<
                super::EcdsaGroup,
                crate::wycheproof::harness::Fields,
            >($file);
            assert!(!file.test_groups.is_empty());
            crate::wycheproof::harness::par_each(&file.test_groups, |g| {
                let public: [u8; 2 * $len + 1] =
                    g.params.public_key.uncompressed.0[..].try_into().unwrap();
                // Wycheproof's compressed points are checked against
                // `compress_public_key` by `compressed_peers`.
                let compressed = $curve::compress_public_key(&public).unwrap();
                assert_eq!($curve::decompress_public_key(&compressed), Some(public));
            });
        }
    };
}

macro_rules! compressed_peers {
    ($test:ident, $curve:ident, $len:literal, $file:literal) => {
        #[test]
        fn $test() {
            use crate::wycheproof::harness::Expectation;
            crate::require_vectors!();
            let file = crate::wycheproof::harness::load::<
                crate::wycheproof::harness::Fields,
                super::EcdhCase,
            >($file);
            let (checked, rejected) = (
                crate::wycheproof::harness::Count::default(),
                crate::wycheproof::harness::Count::default(),
            );
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
                    let key = verified_garbage::ecdh::PrivateKey::<$curve>::from_bytes(&private);
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

mod brainpoolp256r1;
mod brainpoolp384r1;
mod brainpoolp512r1;
mod p192;
mod p224;
mod p256;
mod p384;
mod p521;
mod secp256k1;
