//! The ACVP tests of SLH-DSA (FIPS 205), for each SHAKE parameter set: every
//! vector of key generation (the private and public key of each triple of
//! seeds), and of pure signature generation (hedged, with the vector's
//! `addrnd`, and deterministic) and verification, with the message and its
//! context string, from the downloaded files (`fetched!`).
//! HashSLH-DSA and the internal interface (`M′` given) are not provided, so
//! their vectors are skipped.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::json_struct;

json_struct! {
    pub struct File<T> {
        #[json(rename = "testGroups")]
        pub groups: Vec<Group<T>>,
    }
}

json_struct! {
    pub struct Group<T> {
        #[json(rename = "parameterSet")]
        pub parameter_set: String,
        #[json(rename = "signatureInterface", default)]
        pub interface: String,
        #[json(rename = "preHash", default)]
        pub pre_hash: String,
        #[json(default)]
        pub deterministic: bool,
        pub tests: Vec<T>,
    }
}

json_struct! {
    pub struct KeyGen {
        #[json(rename = "skSeed")]
        pub sk_seed: String,
        #[json(rename = "skPrf")]
        pub sk_prf: String,
        #[json(rename = "pkSeed")]
        pub pk_seed: String,
        pub sk: String,
        pub pk: String,
    }
}

json_struct! {
    pub struct SigGen {
        pub sk: String,
        #[json(rename = "additionalRandomness", default)]
        pub addrnd: String,
        pub message: String,
        #[json(default)]
        pub context: String,
        pub signature: String,
    }
}

json_struct! {
    pub struct SigVer {
        pub pk: String,
        pub message: String,
        #[json(default)]
        pub context: String,
        pub signature: String,
        #[json(rename = "testPassed")]
        pub passed: bool,
    }
}

/// The groups of the parameter set `name` in the vendored file `json` that
/// test pure SLH-DSA with a context string.
pub fn groups<T: crate::json::FromJson>(name: &str, json: &str) -> Vec<Group<T>> {
    let file: File<T> = crate::json::parse(name, json);
    let groups: Vec<Group<T>> = file
        .groups
        .into_iter()
        .filter(|g| g.parameter_set == name)
        .filter(|g| g.interface.is_empty() || (g.interface == "external" && g.pre_hash == "pure"))
        .collect();
    assert!(!groups.is_empty());
    groups
}

/// Defines the tests of the parameter set named `$name`
/// (`"SLH-DSA-SHAKE-128s"`), of the module `$module`
/// (`verified_garbage::slhdsa_shake_128s`, …), whose seeds are `$n` bytes;
/// `$fast` says whether it is a fast-signing (`f`) set.
macro_rules! slhdsa_tests {
    ($name:literal, $module:ident, $n:literal, $fast:literal) => {
        use super::slhdsa::{KeyGen, SigGen, SigVer, groups};
        use verified_garbage::error::{InvalidSignature, SlhDsaError};
        use verified_garbage::$module::{SigningKey, VerifyingKey};

        use verified_garbage_test_vectors::unhex;

        #[test]
        fn keygen() {
            let json = fetched!("SLH-DSA-keyGen-FIPS205/internalProjection.json");
            let mut count = 0;
            for g in groups::<KeyGen>($name, &json) {
                for t in &g.tests {
                    let seeds = [unhex(&t.sk_seed), unhex(&t.sk_prf), unhex(&t.pk_seed)].concat();
                    let key = SigningKey::from_seeds(&seeds[..].try_into().unwrap());
                    assert_eq!(key.as_bytes()[..], unhex(&t.sk)[..]);
                    assert_eq!(key.verifying_key().as_bytes()[..], unhex(&t.pk)[..]);
                    count += 1;
                }
            }
            assert_eq!(count, 10);
        }

        #[test]
        fn siggen() {
            let json = fetched!("SLH-DSA-sigGen-FIPS205/internalProjection.json");
            let mut count = 0;
            for g in groups::<SigGen>($name, &json) {
                for t in &g.tests {
                    let key = SigningKey::from_bytes(&unhex(&t.sk)[..].try_into().unwrap());
                    let (msg, ctx) = (unhex(&t.message), unhex(&t.context));
                    let sig = if g.deterministic {
                        key.sign_deterministic(&msg, &ctx).unwrap()
                    } else {
                        let addrnd: [u8; $n] = unhex(&t.addrnd).try_into().unwrap();
                        key.sign_with_randomness(&msg, &ctx, &addrnd).unwrap()
                    };
                    assert_eq!(sig[..], unhex(&t.signature)[..]);
                    assert_eq!(key.verifying_key().verify(&msg, &ctx, &sig), Ok(()));
                    count += 1;
                }
            }
            assert_eq!(count, 14);
        }

        #[test]
        fn sigver() {
            let json = fetched!("SLH-DSA-sigVer-FIPS205/internalProjection.json");
            let mut count = 0;
            for g in groups::<SigVer>($name, &json) {
                for t in &g.tests {
                    let pk = VerifyingKey::from_bytes(&unhex(&t.pk)[..].try_into().unwrap());
                    let r = pk.verify(&unhex(&t.message), &unhex(&t.context), &unhex(&t.signature));
                    let expected = if t.passed {
                        Ok(())
                    } else {
                        Err(InvalidSignature)
                    };
                    assert_eq!(r, expected);
                    count += 1;
                }
            }
            assert_eq!(count, 14);
        }

        /// Each function once, with as little work as it can do, for a CPU
        /// that is emulated (`ci/cpu_tests.py`'s `slhdsa_once`), on which the
        /// other tests take too long: key generation; signing, of the fast
        /// set (a slow set's refuses a context string that is too long); and
        /// verification, of that signature or of one that is not valid.
        #[test]
        fn once() {
            let key = SigningKey::from_seeds(&[7; 3 * $n]);
            let pk = key.verifying_key();
            let long = [0u8; 256];
            assert_eq!(
                key.sign_deterministic(b"", &long),
                Err(SlhDsaError::ContextTooLong)
            );
            if $fast {
                let sig = key.sign_deterministic(b"message", b"").unwrap();
                assert_eq!(pk.verify(b"message", b"", &sig), Ok(()));
            } else {
                let sig = [0u8; VerifyingKey::SIGNATURE_SIZE];
                assert_eq!(pk.verify(b"message", b"", &sig), Err(InvalidSignature));
            }
        }

        /// Signing, hedged and deterministic, gives signatures that verify;
        /// context strings longer than 255 bytes, and signatures of the
        /// wrong length, are refused.
        #[test]
        fn sign_verify() {
            let key = SigningKey::generate().unwrap();
            let pk = key.verifying_key();
            let sig = key.sign(b"message", b"context").unwrap();
            assert_eq!(pk.verify(b"message", b"context", &sig), Ok(()));
            assert_eq!(pk.verify(b"message", b"other", &sig), Err(InvalidSignature));
            assert_eq!(pk.verify(b"other", b"context", &sig), Err(InvalidSignature));
            assert_eq!(
                pk.verify(b"message", b"context", &sig[1..]),
                Err(InvalidSignature)
            );
            let det = key.sign_deterministic(b"message", b"").unwrap();
            assert_eq!(det, key.sign_deterministic(b"message", b"").unwrap());
            assert_eq!(pk.verify(b"message", b"", &det), Ok(()));
            let long = [0u8; 256];
            assert_eq!(
                key.sign(b"message", &long),
                Err(SlhDsaError::ContextTooLong)
            );
            assert_eq!(
                key.sign_deterministic(b"message", &long),
                Err(SlhDsaError::ContextTooLong)
            );
            assert_eq!(
                key.sign_with_randomness(b"message", &long, &[0; $n]),
                Err(SlhDsaError::ContextTooLong)
            );
            assert_eq!(pk.verify(b"message", &long, &sig), Err(InvalidSignature));
            // Keys are their bytes.
            assert_eq!(VerifyingKey::from_bytes(pk.as_bytes()), pk);
            assert_eq!(
                SigningKey::from_bytes(key.as_bytes()).as_bytes(),
                key.as_bytes()
            );
            assert_eq!(VerifyingKey::SIZE, 2 * $n);
            assert_eq!(VerifyingKey::SIGNATURE_SIZE, sig.len());
            assert_eq!(SigningKey::SIZE, 4 * $n);
            assert_eq!(SigningKey::SEED_SIZE, $n);
            assert!(format!("{key:?}").starts_with("SigningKey"));
            assert!(format!("{pk:?}").starts_with("VerifyingKey"));
        }
    };
}

pub(crate) use slhdsa_tests;
