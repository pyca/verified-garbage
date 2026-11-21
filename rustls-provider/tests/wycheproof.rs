//! The provider's signature verification algorithms and TLS 1.3 HKDF
//! against Wycheproof's test vectors (`WYCHEPROOF_ROOT`: a checkout of
//! C2SP/wycheproof).

use std::path::PathBuf;

use pki_types::SignatureVerificationAlgorithm;
use rustls_verified_garbage as provider;
use serde_json::Value;

fn root() -> PathBuf {
    let root = std::env::var_os("WYCHEPROOF_ROOT")
        .expect("set WYCHEPROOF_ROOT to a checkout of C2SP/wycheproof");
    PathBuf::from(root).join("testvectors_v1")
}

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// The `subjectPublicKey` of a DER `SubjectPublicKeyInfo`, as webpki
/// passes it to a verification algorithm.
#[allow(clippy::result_large_err)] // in the code rust-asn1's derive generates
fn subject_public_key(spki: &[u8]) -> Vec<u8> {
    #[derive(asn1::Asn1Read)]
    struct Spki<'a> {
        _algorithm: asn1::Tlv<'a>,
        subject_public_key: asn1::BitString<'a>,
    }
    let spki = asn1::parse_single::<Spki<'_>>(spki).unwrap();
    spki.subject_public_key.as_bytes().to_vec()
}

/// Checks `alg` against every test of `file`; returns how many ran.
fn check(file: &str, alg: &dyn SignatureVerificationAlgorithm) -> usize {
    let data = std::fs::read(root().join(file)).unwrap();
    let json: Value = serde_json::from_slice(&data).unwrap();
    let mut n = 0;
    for group in json["testGroups"].as_array().unwrap() {
        let key = subject_public_key(&hex(group["publicKeyDer"].as_str().unwrap()));
        for test in group["tests"].as_array().unwrap() {
            // ML-DSA's tests with a context string: TLS signs without one.
            if test.get("ctx").is_some_and(|c| c.as_str() != Some("")) {
                continue;
            }
            let msg = hex(test["msg"].as_str().unwrap());
            let sig = hex(test["sig"].as_str().unwrap());
            let ok = alg.verify_signature(&key, &msg, &sig).is_ok();
            let id = &test["tcId"];
            match test["result"].as_str().unwrap() {
                "valid" => assert!(ok, "{file} test {id}: valid signature rejected"),
                "invalid" => assert!(!ok, "{file} test {id}: invalid signature accepted"),
                _ => {}
            }
            n += 1;
        }
    }
    assert!(n > 0, "{file}: no tests");
    n
}

#[test]
fn ecdsa() {
    for (file, alg) in [
        (
            "ecdsa_secp256r1_sha256_test.json",
            provider::ECDSA_P256_SHA256,
        ),
        (
            "ecdsa_secp256r1_sha512_test.json",
            provider::ECDSA_P256_SHA512,
        ),
        (
            "ecdsa_secp384r1_sha256_test.json",
            provider::ECDSA_P384_SHA256,
        ),
        (
            "ecdsa_secp384r1_sha384_test.json",
            provider::ECDSA_P384_SHA384,
        ),
        (
            "ecdsa_secp384r1_sha512_test.json",
            provider::ECDSA_P384_SHA512,
        ),
        (
            "ecdsa_secp521r1_sha512_test.json",
            provider::ECDSA_P521_SHA512,
        ),
    ] {
        check(file, alg);
    }
}

#[test]
fn ed25519() {
    check("ed25519_test.json", provider::ED25519);
}

#[test]
fn rsa_pkcs1() {
    for (file, alg) in [
        (
            "rsa_signature_2048_sha256_test.json",
            provider::RSA_PKCS1_2048_8192_SHA256,
        ),
        (
            "rsa_signature_2048_sha384_test.json",
            provider::RSA_PKCS1_2048_8192_SHA384,
        ),
        (
            "rsa_signature_2048_sha512_test.json",
            provider::RSA_PKCS1_2048_8192_SHA512,
        ),
        (
            "rsa_signature_3072_sha256_test.json",
            provider::RSA_PKCS1_2048_8192_SHA256,
        ),
        (
            "rsa_signature_3072_sha384_test.json",
            provider::RSA_PKCS1_2048_8192_SHA384,
        ),
        (
            "rsa_signature_3072_sha384_test.json",
            provider::RSA_PKCS1_3072_8192_SHA384,
        ),
        (
            "rsa_signature_3072_sha512_test.json",
            provider::RSA_PKCS1_2048_8192_SHA512,
        ),
        (
            "rsa_signature_4096_sha256_test.json",
            provider::RSA_PKCS1_2048_8192_SHA256,
        ),
        (
            "rsa_signature_4096_sha384_test.json",
            provider::RSA_PKCS1_2048_8192_SHA384,
        ),
        (
            "rsa_signature_4096_sha512_test.json",
            provider::RSA_PKCS1_2048_8192_SHA512,
        ),
    ] {
        check(file, alg);
    }
}

#[test]
fn rsa_pss() {
    for (file, alg) in [
        (
            "rsa_pss_2048_sha256_mgf1_32_test.json",
            provider::RSA_PSS_2048_8192_SHA256_LEGACY_KEY,
        ),
        (
            "rsa_pss_2048_sha384_mgf1_48_test.json",
            provider::RSA_PSS_2048_8192_SHA384_LEGACY_KEY,
        ),
        (
            "rsa_pss_3072_sha256_mgf1_32_test.json",
            provider::RSA_PSS_2048_8192_SHA256_LEGACY_KEY,
        ),
        (
            "rsa_pss_4096_sha256_mgf1_32_test.json",
            provider::RSA_PSS_2048_8192_SHA256_LEGACY_KEY,
        ),
        (
            "rsa_pss_4096_sha384_mgf1_48_test.json",
            provider::RSA_PSS_2048_8192_SHA384_LEGACY_KEY,
        ),
        (
            "rsa_pss_4096_sha512_mgf1_64_test.json",
            provider::RSA_PSS_2048_8192_SHA512_LEGACY_KEY,
        ),
    ] {
        check(file, alg);
    }
}

#[test]
fn ml_dsa() {
    for (file, alg) in [
        ("mldsa_44_verify_test.json", provider::ML_DSA_44),
        ("mldsa_65_verify_test.json", provider::ML_DSA_65),
        ("mldsa_87_verify_test.json", provider::ML_DSA_87),
    ] {
        check(file, alg);
    }
}

/// HKDF through each TLS 1.3 suite's `hkdf_provider`: an extract, then an
/// expand to the test's length, which fails past 255 blocks.
#[test]
fn hkdf() {
    use provider::cipher_suite::{TLS13_AES_128_GCM_SHA256, TLS13_AES_256_GCM_SHA384};
    for (file, suite) in [
        ("hkdf_sha256_test.json", TLS13_AES_128_GCM_SHA256),
        ("hkdf_sha384_test.json", TLS13_AES_256_GCM_SHA384),
    ] {
        let data = std::fs::read(root().join(file)).unwrap();
        let json: Value = serde_json::from_slice(&data).unwrap();
        let mut n = 0;
        for group in json["testGroups"].as_array().unwrap() {
            for test in group["tests"].as_array().unwrap() {
                let ikm = hex(test["ikm"].as_str().unwrap());
                let salt = hex(test["salt"].as_str().unwrap());
                let info = hex(test["info"].as_str().unwrap());
                let size = test["size"].as_u64().unwrap() as usize;
                let expander = suite.hkdf_provider.extract_from_secret(Some(&salt), &ikm);
                let mut okm = vec![0u8; size];
                let ok = expander.expand_slice(&[&info], &mut okm).is_ok();
                let id = &test["tcId"];
                match test["result"].as_str().unwrap() {
                    "valid" => {
                        assert!(ok, "{file} test {id}: rejected");
                        assert_eq!(okm, hex(test["okm"].as_str().unwrap()), "{file} test {id}");
                    }
                    "invalid" => assert!(!ok, "{file} test {id}: accepted"),
                    _ => {}
                }
                n += 1;
            }
        }
        assert!(n > 0, "{file}: no tests");
    }
}
