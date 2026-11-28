//! What the SLH-DSA benchmarks share: `slhdsa_bench!`, the benchmarks of one
//! parameter set, and OpenSSL's keys and operations through `openssl-sys`
//! (rust-openssl names no SLH-DSA key type).
//!
//! OpenSSL implements SLH-DSA from version 3.5; the runners use 3.0. Enable
//! `openssl-slhdsa` on a supported host for the comparison. Key generation
//! is from seeds (verified-garbage) and from fresh randomness (OpenSSL),
//! which is the same work. Signing is pure, with an empty context, hedged in
//! both libraries, and deterministic for verified-garbage's alone;
//! verification verifies one signature. The ids' sizes are the signature's
//! bytes for signing and the message's for verification.

/// OpenSSL's SLH-DSA, for the comparison.
#[cfg(feature = "openssl-slhdsa")]
pub mod openssl_slhdsa {
    use foreign_types::ForeignType;
    use openssl::pkey::{PKey, Private, Public};

    /// The private key `sk` of the algorithm `name` (`c"SLH-DSA-SHAKE-128f"`).
    pub fn private_key(name: &std::ffi::CStr, sk: &[u8]) -> PKey<Private> {
        // SAFETY: `name` is a C string and `sk` is valid for reads of its
        // length; a non-null result is a key that the `PKey` owns.
        unsafe {
            let p = openssl_sys::EVP_PKEY_new_raw_private_key_ex(
                std::ptr::null_mut(),
                name.as_ptr(),
                std::ptr::null(),
                sk.as_ptr(),
                sk.len(),
            );
            assert!(!p.is_null());
            PKey::from_ptr(p)
        }
    }

    /// The public key `pk` of the algorithm `name`.
    pub fn public_key(name: &std::ffi::CStr, pk: &[u8]) -> PKey<Public> {
        // SAFETY: as `private_key`.
        unsafe {
            let p = openssl_sys::EVP_PKEY_new_raw_public_key_ex(
                std::ptr::null_mut(),
                name.as_ptr(),
                std::ptr::null(),
                pk.as_ptr(),
                pk.len(),
            );
            assert!(!p.is_null());
            PKey::from_ptr(p)
        }
    }

    /// A fresh key of the algorithm `name`.
    pub fn generate(name: &std::ffi::CStr) -> PKey<Private> {
        // SAFETY: the context is created from a C string, freed once, and
        // a non-null key is owned by the `PKey`.
        unsafe {
            let ctx = openssl_sys::EVP_PKEY_CTX_new_from_name(std::ptr::null_mut(), name.as_ptr(), std::ptr::null());
            assert!(!ctx.is_null());
            assert_eq!(openssl_sys::EVP_PKEY_keygen_init(ctx), 1);
            let mut p = std::ptr::null_mut();
            assert_eq!(openssl_sys::EVP_PKEY_generate(ctx, &mut p), 1);
            openssl_sys::EVP_PKEY_CTX_free(ctx);
            PKey::from_ptr(p)
        }
    }
}

/// Defines `bench` for the parameter set `$name`
/// (`"slhdsa_shake_128f"`, the groups' prefix) of the module `$module`,
/// named `$ossl` in OpenSSL.
macro_rules! slhdsa_bench {
    ($name:literal, $module:ident, $ossl:literal, $sig:literal) => {
        use criterion::Criterion;

        #[cfg(target_arch = "x86_64")]
        pub fn bench(c: &mut Criterion) {
            use std::hint::black_box;

            use criterion::BenchmarkId;
            use verified_garbage::$module::{SigningKey, VerifyingKey};

            use crate::{BenchDyn, VG};

            let seeds = [0x42; 3 * SigningKey::SEED_SIZE];
            let key = SigningKey::from_seeds(&seeds);
            let pk = key.verifying_key();
            let msg = [0x5a; 64];
            let sig = key.sign_deterministic(&msg, b"").unwrap();
            pk.verify(&msg, b"", &sig).unwrap();
            #[cfg(feature = "openssl-slhdsa")]
            let (openssl_key, openssl_public) = {
                use openssl::sign::{Signer, Verifier};

                use super::slhdsa::openssl_slhdsa::{private_key, public_key};

                let openssl_key = private_key($ossl, key.as_bytes());
                let openssl_public = public_key($ossl, pk.as_bytes());
                assert!(
                    Verifier::new_without_digest(&openssl_public)
                        .unwrap()
                        .verify_oneshot(&sig, &msg)
                        .unwrap()
                );
                let openssl_sig = Signer::new_without_digest(&openssl_key)
                    .unwrap()
                    .sign_oneshot_to_vec(&msg)
                    .unwrap();
                pk.verify(&msg, b"", &openssl_sig).unwrap();
                (openssl_key, openssl_public)
            };
            let mut g = c.benchmark_group(concat!($name, "_keygen"));
            g.sample_size(10);
            g.bench(BenchmarkId::new(VG, VerifyingKey::SIZE), |b| {
                b.iter(|| SigningKey::from_seeds(black_box(&seeds)))
            });
            #[cfg(feature = "openssl-slhdsa")]
            g.bench(BenchmarkId::new(crate::OPENSSL, VerifyingKey::SIZE), |b| {
                b.iter(|| super::slhdsa::openssl_slhdsa::generate($ossl))
            });
            g.finish();
            let mut g = c.benchmark_group(concat!($name, "_sign"));
            g.sample_size(10);
            g.bench(BenchmarkId::new(VG, $sig), |b| b.iter(|| key.sign(black_box(&msg), b"").unwrap()));
            #[cfg(feature = "openssl-slhdsa")]
            g.bench(BenchmarkId::new(crate::OPENSSL, $sig), |b| {
                b.iter(|| {
                    openssl::sign::Signer::new_without_digest(&openssl_key)
                        .unwrap()
                        .sign_oneshot_to_vec(black_box(&msg))
                        .unwrap()
                })
            });
            g.finish();
            let mut g = c.benchmark_group(concat!($name, "_sign_deterministic"));
            g.sample_size(10);
            g.bench(BenchmarkId::new(VG, $sig), |b| {
                b.iter(|| key.sign_deterministic(black_box(&msg), b"").unwrap())
            });
            g.finish();
            let mut g = c.benchmark_group(concat!($name, "_verify"));
            g.bench(BenchmarkId::new(VG, msg.len()), |b| {
                b.iter(|| pk.verify(black_box(&msg), b"", black_box(&sig)).unwrap())
            });
            #[cfg(feature = "openssl-slhdsa")]
            g.bench(BenchmarkId::new(crate::OPENSSL, msg.len()), |b| {
                b.iter(|| {
                    assert!(
                        openssl::sign::Verifier::new_without_digest(&openssl_public)
                            .unwrap()
                            .verify_oneshot(black_box(&sig), black_box(&msg))
                            .unwrap()
                    )
                })
            });
            g.finish();
        }

        #[cfg(not(target_arch = "x86_64"))]
        pub fn bench(_: &mut Criterion) {}
    };
}

pub(crate) use slhdsa_bench;
