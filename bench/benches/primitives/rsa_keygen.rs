//! The generation of an RSA key's prime, and the test of one candidate that
//! is prime.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa_keygen"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use verified_garbage::rsa_keygen::{generate_prime, generate_prime_from};

    use crate::{OPENSSL, VG};
    // The primes of keys of 2048, 3072 and 4096 bits; the ids' size is the
    // prime's bytes. Each library draws candidates from the operating
    // system's random number generator until one is a probable prime (with
    // the public exponent 65537 for verified-garbage, which also tests
    // `gcd(p - 1, e)`), so that the time varies from one prime to the next.
    let mut g = c.benchmark_group("rsa_keygen_prime");
    g.sample_size(10);
    for bits in [1024, 1536, 2048] {
        g.bench_function(BenchmarkId::new(VG, bits / 8), |b| {
            b.iter(|| generate_prime(black_box(bits), black_box(&[1, 0, 1]), None).unwrap())
        });
        g.bench_function(BenchmarkId::new(OPENSSL, bits / 8), |b| {
            b.iter(|| {
                let mut p = BigNum::new().unwrap();
                p.generate_prime(black_box(bits as i32), false, None, None)
                    .unwrap();
                p
            })
        });
    }
    g.finish();

    // The same sizes: the test of one candidate that is a prime (one OpenSSL
    // generated, whose two top bits it sets), which is most of a generation's
    // time: trial division, then 16 rounds of Miller–Rabin with witnesses
    // from octets drawn once (verified-garbage's 16 at these sizes, after
    // `gcd(p - 1, e)` with `e = 65537`; OpenSSL's `BN_is_prime_fasttest_ex`).
    let mut g = c.benchmark_group("rsa_keygen_test");
    g.sample_size(10);
    for bits in [1024, 1536, 2048] {
        let mut p = BigNum::new().unwrap();
        p.generate_prime(bits as i32, false, None, None).unwrap();
        let prime = p.to_vec();
        let mut rand = prime.clone();
        rand.extend((0..64 * prime.len()).map(|i| (i * 37 + 11) as u8));
        assert_eq!(
            generate_prime_from(bits, &[1, 0, 1], None, &rand)
                .unwrap()
                .0,
            prime
        );
        let mut ctx = BigNumContext::new().unwrap();
        g.bench_function(BenchmarkId::new(VG, bits / 8), |b| {
            b.iter(|| {
                generate_prime_from(
                    black_box(bits),
                    black_box(&[1, 0, 1]),
                    None,
                    black_box(&rand),
                )
                .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, bits / 8), |b| {
            b.iter(|| assert!(black_box(&p).is_prime_fasttest(16, &mut ctx, true).unwrap()))
        });
    }
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
