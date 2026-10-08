//! The RSA public-key operation (RSAEP), without padding, and the loading
//! of a public key.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::rsa::{PublicEncryptingKey, PublicKeyComponents};
    use criterion::BenchmarkId;
    use openssl::bn::BigNum;
    use openssl::rsa::{Padding, Rsa};
    use verified_garbage::rsa::PublicKey;

    use crate::{AWS_LC, OPENSSL, VG};
    let mut g = c.benchmark_group("rsa_public");
    // Moduli of 2048, 3072 and 4096 bits with the exponent 65537; the ids'
    // size is the modulus' bytes. Each library loads the key once, outside
    // the measurements, as a verifier holds a public key across operations.
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e) = (key.n().to_vec(), key.e().to_vec());
        let k = n.len();
        let vg_key = PublicKey::new(&n, &e).unwrap();
        let openssl_key = Rsa::from_public_components(
            BigNum::from_slice(&n).unwrap(),
            BigNum::from_slice(&e).unwrap(),
        )
        .unwrap();
        // An input below the modulus.
        let mut input = vec![0x42; k];
        input[0] = 0;
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                black_box(&vg_key)
                    .public_op(black_box(&input), &mut out)
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                black_box(&openssl_key)
                    .public_encrypt(black_box(&input), &mut out, Padding::NONE)
                    .unwrap()
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("rsa_public_key");
    // The same sizes: loading a public key from `(n, e)`, as each library
    // does it. OpenSSL and AWS-LC set up the Montgomery values of `n` at the
    // key's first operation, not here (`rsa_public_once` counts them).
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e) = (key.n().to_vec(), key.e().to_vec());
        let k = n.len();
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| PublicKey::new(black_box(&n), black_box(&e)).unwrap())
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                Rsa::from_public_components(
                    BigNum::from_slice(black_box(&n)).unwrap(),
                    BigNum::from_slice(black_box(&e)).unwrap(),
                )
                .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(AWS_LC, k), |b| {
            b.iter(|| {
                let c = PublicKeyComponents {
                    n: black_box(&n),
                    e: black_box(&e),
                };
                TryInto::<PublicEncryptingKey>::try_into(c).unwrap()
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("rsa_public_once");
    // The same sizes: loading a public key and its first operation, as a
    // verifier of a certificate's signature uses its key once.
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e) = (key.n().to_vec(), key.e().to_vec());
        let k = n.len();
        let mut input = vec![0x42; k];
        input[0] = 0;
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                PublicKey::new(black_box(&n), black_box(&e))
                    .unwrap()
                    .public_op(black_box(&input), &mut out)
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                Rsa::from_public_components(
                    BigNum::from_slice(black_box(&n)).unwrap(),
                    BigNum::from_slice(black_box(&e)).unwrap(),
                )
                .unwrap()
                .public_encrypt(black_box(&input), &mut out, Padding::NONE)
                .unwrap()
            })
        });
    }
    g.finish();
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
