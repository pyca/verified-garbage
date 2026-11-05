//! The loading of an RSA public key.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::rsa::{PublicEncryptingKey, PublicKeyComponents};
    use criterion::BenchmarkId;
    use openssl::bn::BigNum;
    use openssl::rsa::Rsa;
    use verified_garbage::rsa::{BigUint, PublicKey};

    use crate::{AWS_LC, BenchDyn, OPENSSL, VG};
    let mut g = c.benchmark_group("rsa_public_key");
    // Moduli of 2048, 3072 and 4096 bits with the exponent 65537; the ids'
    // size is the modulus' bytes: loading a public key from `(n, e)`, as each
    // library does it. OpenSSL and AWS-LC set up the Montgomery values of `n`
    // at the key's first operation, not here, as verified-garbage does (the
    // operations' benchmarks with a key loaded once measure them).
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e) = (key.n().to_vec(), key.e().to_vec());
        let k = n.len();
        g.bench(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                PublicKey::new(
                    BigUint::from_be_bytes(black_box(&n)),
                    BigUint::from_be_bytes(black_box(&e)),
                )
                .unwrap()
            })
        });
        g.bench(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                Rsa::from_public_components(
                    BigNum::from_slice(black_box(&n)).unwrap(),
                    BigNum::from_slice(black_box(&e)).unwrap(),
                )
                .unwrap()
            })
        });
        g.bench(BenchmarkId::new(AWS_LC, k), |b| {
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
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
