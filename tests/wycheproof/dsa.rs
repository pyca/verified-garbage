//! DSA P1363 verification: scalar ranges, malformed signatures and edge cases.
#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        all(target_arch = "powerpc64", target_endian = "little")
    ),
    feature = "alloc"
))]

use super::harness::{self, Count, Expectation, Hex};
use crate::json_struct;
use crate::require_vectors;
use verified_garbage::dsa::PublicKey;
use verified_garbage::hashes::{sha224::Sha224, sha256::Sha256};

json_struct! {
    struct Key {
        p: Hex,
        q: Hex,
        g: Hex,
        y: Hex,
        #[json(rename = "keySize")]
        bits: usize,
    }
}

json_struct! {
    struct Group {
        #[json(rename = "publicKey")]
        public_key: Key,
        sha: String,
    }
}

json_struct! {
    struct Case {
        msg: Hex,
        sig: Hex,
    }
}

fn pad(value: &[u8], width: usize) -> Vec<u8> {
    let value = crate::bytes::trim_zeros(value);
    assert!(value.len() <= width);
    let mut result = vec![0; width - value.len()];
    result.extend_from_slice(value);
    result
}

#[test]
fn signatures() {
    require_vectors!();
    for (name, q_len) in [
        ("dsa_2048_224_sha224_p1363_test.json", 28),
        ("dsa_2048_224_sha256_p1363_test.json", 28),
        ("dsa_2048_256_sha256_p1363_test.json", 32),
        ("dsa_3072_256_sha256_p1363_test.json", 32),
    ] {
        let file = harness::load::<Group, Case>(name);
        let (verified, refused) = (Count::default(), Count::default());
        file.par_tests(|group, test| {
            let k = &group.params.public_key;
            let p_len = k.bits / 8;
            let key = PublicKey::from_components(
                &pad(&k.p.0, p_len),
                &pad(&k.q.0, q_len),
                &pad(&k.g.0, p_len),
                &pad(&k.y.0, p_len),
            )
            .unwrap();
            let digest = if group.params.sha == "SHA-224" {
                Sha224::digest(&test.case.msg.0).to_vec()
            } else {
                assert_eq!(group.params.sha, "SHA-256");
                Sha256::digest(&test.case.msg.0).to_vec()
            };
            let valid = key.verify(&digest, &test.case.sig.0);
            match test.result {
                Expectation::Valid => {
                    assert!(valid, "{name} tcId {}", test.tc_id);
                    verified.add();
                }
                Expectation::Invalid | Expectation::Acceptable => {
                    assert!(!valid, "{name} tcId {}", test.tc_id);
                    refused.add();
                }
            }
        });
        assert!(verified.get() > 0 && refused.get() > 0);
    }
}
