//! The benchmarks of ML-KEM, for each parameter set: key generation from a
//! seed, encapsulation and decapsulation, beside OpenSSL and aws-lc-rs.
//!
//! OpenSSL implements ML-KEM from version 3.5, which the runners' OpenSSL
//! (3.0) predates. Enable `openssl-mlkem` on a supported host for the comparison.
//! Keys are expanded before timing encapsulation/decapsulation; OpenSSL and
//! aws-lc-rs create a fresh operation context each iteration. All
//! encapsulators use fresh randomness. Key generation includes expansion from
//! the same seed. aws-lc-rs does not wrap AWS-LC's key generation from a seed,
//! so that benchmark calls AWS-LC through aws-lc-sys, importing the seed as
//! a PKCS #8 key (RFC 9935's `seed` form, which AWS-LC expands), and
//! aws-lc-rs decapsulates with the expanded key it generates.
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
    ($c:expr, verified_garbage::$module:ident, $DecapsulationKey:ident, $EncapsulationKey:ident, $key_type:ident, $aws_lc:ident) => {{
        use std::hint::black_box;

        use criterion::BenchmarkId;
        use verified_garbage::$module::{$DecapsulationKey, $EncapsulationKey};

        use crate::{AWS_LC, VG};
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
        let aws_lc_alg = &aws_lc_rs::kem::$aws_lc;
        let aws_lc_public =
            aws_lc_rs::kem::EncapsulationKey::new(aws_lc_alg, ek.as_bytes()).unwrap();
        let (ciphertext, ss) = aws_lc_public.encapsulate().unwrap();
        assert_eq!(
            &dk.decapsulate(ciphertext.as_ref().try_into().unwrap())
                .unwrap(),
            ss.as_ref()
        );
        let aws_lc_seed_key = crate::mlkem::AwsLcKey::from_seed(aws_lc_alg, &seed);
        let mut aws_lc_ek = [0; $EncapsulationKey::SIZE];
        aws_lc_seed_key.raw_public_key(&mut aws_lc_ek);
        assert_eq!(&aws_lc_ek, ek.as_bytes());
        let aws_lc_key =
            aws_lc_rs::kem::DecapsulationKey::new(aws_lc_alg, &aws_lc_seed_key.raw_private_key())
                .unwrap();
        assert_eq!(
            aws_lc_key.decapsulate((&ct[..]).into()).unwrap().as_ref(),
            _ss
        );
        // Both libraries must also implement implicit rejection identically.
        let mut invalid = ct;
        invalid[0] ^= 1;
        assert_eq!(
            aws_lc_key
                .decapsulate((&invalid[..]).into())
                .unwrap()
                .as_ref(),
            dk.decapsulate(&invalid).unwrap()
        );
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
        g.bench_function(
            BenchmarkId::new(AWS_LC, $EncapsulationKey::SIZE + 64),
            |b| {
                b.iter(|| {
                    crate::mlkem::AwsLcKey::from_seed(aws_lc_alg, black_box(&seed))
                        .raw_public_key(&mut aws_lc_ek)
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
        g.bench_function(
            BenchmarkId::new(AWS_LC, $EncapsulationKey::CIPHERTEXT_SIZE + 32),
            |b| b.iter(|| black_box(&aws_lc_public).encapsulate().unwrap()),
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
        g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
            b.iter(|| {
                black_box(&aws_lc_key)
                    .decapsulate(black_box(&ct[..]).into())
                    .unwrap()
            })
        });
        g.finish();
    }};
}

pub(crate) use mlkem_bench;

/// An AWS-LC ML-KEM key, generated from a seed, which aws-lc-rs does not
/// wrap.
pub(crate) struct AwsLcKey(*mut aws_lc_sys::EVP_PKEY);

impl AwsLcKey {
    /// The key of `alg` from the 64-byte seed `d || z` (FIPS 203's
    /// `ML-KEM.KeyGen_internal`), which AWS-LC expands when it parses the
    /// seed as a PKCS #8 `PrivateKeyInfo` (RFC 9935's `seed [0]` choice).
    /// (aws-lc-sys's universal bindings, ARMv7's, have no
    /// `EVP_PKEY_keygen_deterministic`.)
    pub(crate) fn from_seed(alg: &aws_lc_rs::kem::Algorithm, seed: &[u8; 64]) -> Self {
        use aws_lc_rs::kem::AlgorithmId;
        // The last arc of the algorithm's OID, 2.16.840.1.101.3.4.4.n (RFC 9935).
        let arc = match alg.id() {
            AlgorithmId::MlKem512 => 1,
            AlgorithmId::MlKem768 => 2,
            AlgorithmId::MlKem1024 => 3,
            _ => unreachable!(),
        };
        let mut der = [0; 86];
        der[..22].copy_from_slice(&[
            0x30, 0x54, // PrivateKeyInfo
            0x02, 0x01, 0x00, // version 0
            0x30, 0x0b, // AlgorithmIdentifier
            0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, arc, // its OID
            0x04, 0x42, // privateKey
            0x80, 0x40, // seed [0] IMPLICIT OCTET STRING
        ]);
        der[22..].copy_from_slice(seed);
        let mut cbs = aws_lc_sys::CBS {
            data: der.as_ptr(),
            len: der.len(),
        };
        // SAFETY: cbs points to der, which outlives the call.
        let key = unsafe { aws_lc_sys::EVP_parse_private_key(&mut cbs) };
        assert!(!key.is_null() && cbs.len == 0);
        Self(key)
    }

    /// Writes the encapsulation key to `out`, which must be its size.
    pub(crate) fn raw_public_key(&self, out: &mut [u8]) {
        let mut len = out.len();
        // SAFETY: self.0 is a live key; out is writable for len bytes.
        let ok =
            unsafe { aws_lc_sys::EVP_PKEY_get_raw_public_key(self.0, out.as_mut_ptr(), &mut len) };
        assert_eq!((ok, len), (1, out.len()));
    }

    /// The expanded decapsulation key, as aws-lc-rs's
    /// `DecapsulationKey::new` takes it.
    pub(crate) fn raw_private_key(&self) -> Vec<u8> {
        let mut len = 0;
        // SAFETY: self.0 is a live key; a null output queries the size.
        let ok = unsafe {
            aws_lc_sys::EVP_PKEY_get_raw_private_key(self.0, std::ptr::null_mut(), &mut len)
        };
        assert_eq!(ok, 1);
        let mut out = vec![0; len];
        // SAFETY: self.0 is a live key; out is writable for len bytes.
        let ok =
            unsafe { aws_lc_sys::EVP_PKEY_get_raw_private_key(self.0, out.as_mut_ptr(), &mut len) };
        assert_eq!((ok, len), (1, out.len()));
        out
    }
}

impl Drop for AwsLcKey {
    fn drop(&mut self) {
        // SAFETY: self.0 is a live key that nothing else frees.
        unsafe { aws_lc_sys::EVP_PKEY_free(self.0) }
    }
}

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
