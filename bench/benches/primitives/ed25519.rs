//! Ed25519 key derivation, signing, and verification beside OpenSSL and
//! aws-lc-rs.

use criterion::Criterion;

pub const USES: &[&str] = &["ed25519", "sha512"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::signature::{ED25519, Ed25519KeyPair, KeyPair, ParsedPublicKey};
    use criterion::BenchmarkId;
    use openssl::pkey::{Id, PKey};
    use openssl::sign::{Signer, Verifier};
    use verified_garbage::ed25519::{SigningKey, VerifyingKey};

    use crate::{AWS_LC, OPENSSL, SIZES, VG};

    let seed = [0x42; 32];
    let key = SigningKey::from_seed(&seed);
    let public = VerifyingKey::from_bytes(key.verifying_key().as_bytes());
    let openssl_key = PKey::private_key_from_raw_bytes(&seed, Id::ED25519).unwrap();
    let openssl_public = PKey::public_key_from_raw_bytes(public.as_bytes(), Id::ED25519).unwrap();
    let aws_lc_key = Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
    assert_eq!(aws_lc_key.public_key().as_ref(), public.as_bytes());
    let aws_lc_public = ParsedPublicKey::new(&ED25519, public.as_bytes()).unwrap();

    let mut g = c.benchmark_group("ed25519_keygen");
    // THROWAWAY (never merge): the "openssl" column is aws-lc's SHA-512 and
    // s2n-bignum's edwards25519_scalarmulbase_alt and edwards25519_encode,
    // called directly from aws-lc-sys as aws-lc's key derivation does; the
    // "aws-lc-rs" column the same with edwards25519_scalarmulbase.
    unsafe extern "C" {
        fn aws_lc_0_45_0_SHA512(data: *const u8, len: usize, out: *mut u8) -> *mut u8;
        fn aws_lc_0_45_0_edwards25519_scalarmulbase_alt(res: *mut u64, k: *const u64);
        fn aws_lc_0_45_0_edwards25519_scalarmulbase(res: *mut u64, k: *const u64);
        fn aws_lc_0_45_0_edwards25519_encode(z: *mut u8, p: *const u64);
    }
    let s2n = |f: unsafe extern "C" fn(*mut u64, *const u64), seed: &[u8; 32]| {
        let mut az = [0u8; 64];
        unsafe { aws_lc_0_45_0_SHA512(seed.as_ptr(), 32, az.as_mut_ptr()) };
        az[0] &= 248;
        az[31] &= 127;
        az[31] |= 64;
        let mut k = [0u64; 4];
        for (i, w) in k.iter_mut().enumerate() {
            *w = u64::from_le_bytes(az[8 * i..8 * i + 8].try_into().unwrap());
        }
        let mut p = [0u64; 8];
        let mut r = [0u8; 32];
        unsafe {
            f(p.as_mut_ptr(), k.as_ptr());
            aws_lc_0_45_0_edwards25519_encode(r.as_mut_ptr(), p.as_ptr());
        }
        r
    };
    assert_eq!(
        &s2n(aws_lc_0_45_0_edwards25519_scalarmulbase_alt, &seed),
        public.as_bytes()
    );
    assert_eq!(
        &s2n(aws_lc_0_45_0_edwards25519_scalarmulbase, &seed),
        public.as_bytes()
    );
    g.bench_function(BenchmarkId::new(VG, 32), |b| {
        b.iter(|| SigningKey::from_seed(black_box(&seed)))
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 32), |b| {
        b.iter(|| {
            s2n(
                aws_lc_0_45_0_edwards25519_scalarmulbase_alt,
                black_box(&seed),
            )
        })
    });
    g.bench_function(BenchmarkId::new(AWS_LC, 32), |b| {
        b.iter(|| s2n(aws_lc_0_45_0_edwards25519_scalarmulbase, black_box(&seed)))
    });
    g.finish();

    let mut g = c.benchmark_group("ed25519_sign");
    for size in SIZES {
        let message = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| key.sign(black_box(&message)))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                Signer::new_without_digest(&openssl_key)
                    .unwrap()
                    .sign_oneshot_to_vec(black_box(&message))
                    .unwrap()
            })
        });
        assert_eq!(aws_lc_key.sign(&message).as_ref(), key.sign(&message));
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| aws_lc_key.sign(black_box(&message)))
        });
    }
    g.finish();

    let mut g = c.benchmark_group("ed25519_verify");
    for size in SIZES {
        let message = vec![0x5a; size];
        let signature = key.sign(&message);
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                public
                    .verify(black_box(&message), black_box(&signature))
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                Verifier::new_without_digest(&openssl_public)
                    .unwrap()
                    .verify_oneshot(black_box(&signature), black_box(&message))
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                aws_lc_public
                    .verify_sig(black_box(&message), black_box(&signature))
                    .unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm"
)))]
pub fn bench(_: &mut Criterion) {}
