//! RSA's operations sharing a key: PSS and PKCS #1 v1.5 verification and
//! OAEP encryption, which lease the public key's buffer, alternated on
//! threads sharing the key, with the keys of the Wycheproof vectors
//! `rsa_pkcs1_*_test.json`.

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]

use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::rsa_pkcs1_sig;
use verified_garbage::rsa_pss;

use super::harness;
use super::rsa_oaep::keys;
use super::schema::{MsgCase, RsaPrivateKeyGroup};
use crate::require_vectors;

/// With each CRT key of the RSAES-PKCS1-v1_5 decryption vectors
/// (`rsa_pkcs1_*_test.json`), of the sizes the RSA tests run
/// (`harness::rsa_bits_tested`): PSS and PKCS #1 v1.5 verification and OAEP
/// encryption, which lease the public key's buffer, alternated on threads
/// sharing the key.
#[test]
fn rsa_shared_key_leases() {
    require_vectors!();
    for bits in [2048, 3072, 4096]
        .into_iter()
        .filter(|&b| harness::rsa_bits_tested(b))
    {
        shared_key_leases(bits, usize::MAX, 4);
    }
}

/// Concurrent callers with one vector key, for emulated backends; the full
/// stress test remains on native and SKX jobs.
#[test]
fn rsa_shared_key_leases_smoke() {
    require_vectors!();
    shared_key_leases(2048, 1, 1);
}

fn shared_key_leases(bits: usize, groups: usize, repetitions: usize) {
    let name = format!("rsa_pkcs1_{bits}_test.json");
    let file = harness::load::<RsaPrivateKeyGroup, MsgCase>(&name);
    harness::par_each(
        &file.test_groups[..groups.min(file.test_groups.len())],
        |group| {
            let (private, public) = keys(&name, &group.params.private_key);
            // Signature verification and OAEP encryption lease the same key's
            // buffer, with different workspace lengths. Alternate them, including
            // rejected inputs, and share the key across concurrent callers.
            let d = Sha256::digest(&group.tests[0].case.msg.0).as_ref().to_vec();
            let sig = rsa_pkcs1_sig::sign(&private, &d, rsa_pkcs1_sig::Hash::Sha256).unwrap();
            let pss = rsa_pss::sign(
                &private,
                &d,
                rsa_pss::Hash::Sha256,
                rsa_pss::Hash::Sha256,
                0,
            )
            .unwrap();
            std::thread::scope(|scope| {
                for _ in 0..4 {
                    let (public, d, sig, pss) = (&public, &d, &sig, &pss);
                    let private = &private;
                    scope.spawn(move || {
                        for _ in 0..repetitions {
                            assert!(rsa_pkcs1_sig::verify(
                                public,
                                sig,
                                d,
                                rsa_pkcs1_sig::Hash::Sha256
                            ));
                            assert!(!rsa_pkcs1_sig::verify(
                                public,
                                &sig[..sig.len() - 1],
                                d,
                                rsa_pkcs1_sig::Hash::Sha256
                            ));
                            assert!(rsa_pss::verify(
                                public,
                                pss,
                                d,
                                rsa_pss::Hash::Sha256,
                                rsa_pss::Hash::Sha256,
                                rsa_pss::SaltLength::Len(0),
                            ));
                            assert!(!rsa_pkcs1_sig::verify(
                                public,
                                sig,
                                &d[..d.len() - 1],
                                rsa_pkcs1_sig::Hash::Sha256
                            ));
                            let ciphertext = verified_garbage::rsa_oaep::encrypt(
                                public,
                                d,
                                verified_garbage::rsa_oaep::Hash::Sha256,
                                verified_garbage::rsa_oaep::Hash::Sha256,
                                b"",
                            )
                            .unwrap();
                            assert_eq!(
                                verified_garbage::rsa_oaep::decrypt(
                                    private,
                                    &ciphertext,
                                    verified_garbage::rsa_oaep::Hash::Sha256,
                                    verified_garbage::rsa_oaep::Hash::Sha256,
                                    b"",
                                )
                                .unwrap(),
                                *d,
                            );
                            assert!(rsa_pkcs1_sig::verify(
                                public,
                                sig,
                                d,
                                rsa_pkcs1_sig::Hash::Sha256
                            ));
                        }
                    });
                }
            });
        },
    );
}
