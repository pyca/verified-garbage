//! The benchmarks of ML-KEM, for each parameter set: key generation from a
//! seed, encapsulation and decapsulation.
//!
//! OpenSSL implements ML-KEM from version 3.5, which the runners' OpenSSL
//! (3.0) predates. Enable `openssl-mlkem` on a supported host for the comparison.
//! Keys are expanded before timing encapsulation/decapsulation; OpenSSL
//! creates a fresh operation context each iteration. Both encapsulators use
//! fresh randomness. Key generation includes expansion from the same seed.
//! The ids' sizes are the bytes of the output (the keys, the ciphertext and
//! the shared secret key).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

/// Runs, in `$c`, the benchmarks of the module `verified_garbage::$module`
/// and its key types, in groups named after the module.
macro_rules! mlkem_bench {
    ($c:expr, verified_garbage::$module:ident, $DecapsulationKey:ident, $EncapsulationKey:ident, $key_type:ident) => {{
        use std::hint::black_box;

        use criterion::BenchmarkId;
        use verified_garbage::$module::{$DecapsulationKey, $EncapsulationKey};

        use crate::VG;
        let c: &mut criterion::Criterion = $c;
        let seed = [0x42; 64];
        let dk = $DecapsulationKey::from_seed(&seed).unwrap();
        let ek = dk.encapsulation_key();
        // Keep the decapsulation input identical across benchmark binaries.
        // Timed encapsulation below still draws fresh randomness.
        let (_ss, ct) = ek.encapsulate_internal(&[0x42; 32]).unwrap();
        #[cfg(feature = "openssl-mlkem")]
        let (openssl_key, openssl_public) = {
            use openssl::pkey::{KeyType, PKey};
            let key_type = KeyType::$key_type;
            let key = PKey::private_key_from_seed(None, key_type, None, &seed).unwrap();
            let public = key.raw_public_key().unwrap();
            assert_eq!(public.as_slice(), ek.as_bytes());
            let public = PKey::public_key_from_raw_bytes_ex(None, key_type, None, &public).unwrap();
            assert_eq!(crate::mlkem::openssl_decapsulate(&key, &ct), _ss);
            let (ss, ciphertext) = crate::mlkem::openssl_encapsulate::<
                { $EncapsulationKey::CIPHERTEXT_SIZE },
            >(&public);
            assert_eq!(dk.decapsulate(&ciphertext).unwrap(), ss);
            // Both libraries must also implement implicit rejection identically.
            let mut invalid = ct;
            invalid[0] ^= 1;
            assert_eq!(
                dk.decapsulate(&invalid).unwrap(),
                crate::mlkem::openssl_decapsulate(&key, &invalid)
            );
            (key, public)
        };
        let mut g = c.benchmark_group(concat!(stringify!($module), "_keygen"));
        g.bench_function(BenchmarkId::new(VG, $EncapsulationKey::SIZE + 64), |b| {
            b.iter(|| $DecapsulationKey::from_seed(black_box(&seed)).unwrap())
        });
        #[cfg(feature = "openssl-mlkem")]
        g.bench_function(
            BenchmarkId::new(crate::OPENSSL, $EncapsulationKey::SIZE + 64),
            |b| {
                b.iter(|| {
                    openssl::pkey::PKey::private_key_from_seed(
                        None,
                        openssl::pkey::KeyType::$key_type,
                        None,
                        black_box(&seed),
                    )
                    .unwrap()
                    .raw_public_key()
                    .unwrap()
                })
            },
        );
        g.finish();
        let mut g = c.benchmark_group(concat!(stringify!($module), "_encaps"));
        g.bench_function(
            BenchmarkId::new(VG, $EncapsulationKey::CIPHERTEXT_SIZE + 32),
            |b| b.iter(|| black_box(ek).encapsulate().unwrap()),
        );
        #[cfg(feature = "openssl-mlkem")]
        g.bench_function(
            BenchmarkId::new(crate::OPENSSL, $EncapsulationKey::CIPHERTEXT_SIZE + 32),
            |b| {
                b.iter(|| {
                    crate::mlkem::openssl_encapsulate::<{ $EncapsulationKey::CIPHERTEXT_SIZE }>(
                        black_box(&openssl_public),
                    )
                })
            },
        );
        g.finish();
        let mut g = c.benchmark_group(concat!(stringify!($module), "_decaps"));
        g.bench_function(BenchmarkId::new(VG, 32), |b| {
            b.iter(|| dk.decapsulate(black_box(&ct)).unwrap())
        });
        #[cfg(feature = "openssl-mlkem")]
        g.bench_function(BenchmarkId::new(crate::OPENSSL, 32), |b| {
            b.iter(|| crate::mlkem::openssl_decapsulate(black_box(&openssl_key), black_box(&ct)))
        });
        g.finish();
    }};
}

pub(crate) use mlkem_bench;

/// A fresh OpenSSL operation context, with fixed-size outputs like VG's API.
#[cfg(feature = "openssl-mlkem")]
pub(crate) fn openssl_encapsulate<const N: usize>(
    key: &openssl::pkey::PKeyRef<openssl::pkey::Public>,
) -> ([u8; 32], [u8; N]) {
    use foreign_types::ForeignType;
    use openssl::pkey_ctx::PkeyCtx;

    let ctx = PkeyCtx::new(key).unwrap();
    let (mut ct_len, mut ss_len) = (0, 0);
    let (mut ct, mut ss) = ([0; N], [0; 32]);
    // SAFETY: ctx owns a live context for key. Null parameters select defaults;
    // null outputs query sizes, with valid, distinct length pointers.
    unsafe {
        assert_eq!(
            openssl_sys::EVP_PKEY_encapsulate_init(ctx.as_ptr(), std::ptr::null()),
            1
        );
        assert_eq!(
            openssl_sys::EVP_PKEY_encapsulate(
                ctx.as_ptr(),
                std::ptr::null_mut(),
                &mut ct_len,
                std::ptr::null_mut(),
                &mut ss_len
            ),
            1
        );
    }
    assert_eq!((ct_len, ss_len), (ct.len(), ss.len()));
    // SAFETY: the queried sizes match the writable, nonoverlapping output
    // buffers; ctx and the length pointers remain valid for the call.
    unsafe {
        assert_eq!(
            openssl_sys::EVP_PKEY_encapsulate(
                ctx.as_ptr(),
                ct.as_mut_ptr(),
                &mut ct_len,
                ss.as_mut_ptr(),
                &mut ss_len
            ),
            1
        );
    }
    assert_eq!((ct_len, ss_len), (N, 32));
    (ss, ct)
}

#[cfg(feature = "openssl-mlkem")]
pub(crate) fn openssl_decapsulate(
    key: &openssl::pkey::PKeyRef<openssl::pkey::Private>,
    ct: &[u8],
) -> [u8; 32] {
    use foreign_types::ForeignType;
    use openssl::pkey_ctx::PkeyCtx;

    let ctx = PkeyCtx::new(key).unwrap();
    let mut ss_len = 0;
    let mut ss = [0; 32];
    // SAFETY: ctx owns a live context for key; ct is readable for ct.len()
    // bytes. A null output queries the size through a valid length pointer.
    unsafe {
        assert_eq!(
            openssl_sys::EVP_PKEY_decapsulate_init(ctx.as_ptr(), std::ptr::null()),
            1
        );
        assert_eq!(
            openssl_sys::EVP_PKEY_decapsulate(
                ctx.as_ptr(),
                std::ptr::null_mut(),
                &mut ss_len,
                ct.as_ptr(),
                ct.len()
            ),
            1
        );
    }
    assert_eq!(ss_len, ss.len());
    // SAFETY: ss has the queried capacity and does not overlap ct. The context,
    // input slice, output buffer and length pointer are all valid for the call.
    unsafe {
        assert_eq!(
            openssl_sys::EVP_PKEY_decapsulate(
                ctx.as_ptr(),
                ss.as_mut_ptr(),
                &mut ss_len,
                ct.as_ptr(),
                ct.len()
            ),
            1
        );
    }
    assert_eq!(ss_len, ss.len());
    ss
}
