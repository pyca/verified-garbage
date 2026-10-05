//! The generation of an RSA key, of one of its primes, the test of one
//! candidate that is prime, and the key from its two primes.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa_keygen"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use openssl::rsa::Rsa;
    use verified_garbage::rsa_keygen::{generate_from, generate_prime_from, key_from_primes};

    use crate::{OPENSSL, VG};
    // The primes of keys of 2048, 3072 and 4096 bits; the ids' size is the
    // prime's bytes. Each library draws candidates until one is a probable
    // prime (with the public exponent 65537 for verified-garbage, which also
    // tests `gcd(p - 1, e)`). The number of candidates varies from one prime
    // to the next, so verified-garbage reads the same octets in every run, a
    // stream from a fixed seed (splitmix64, long enough for its prime), and
    // a slowdown is the code's, not the draw's: it is
    // `generate_prime(bits, e, None)` but for `getrandom`. OpenSSL draws
    // from its own generator.
    let mut g = c.benchmark_group("rsa_keygen_prime");
    g.sample_size(10);
    for bits in [1024, 1536, 2048] {
        let rand = fixed_octets(bits, |r| {
            generate_prime_from(bits, &[1, 0, 1], None, r).is_ok()
        });
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
            b.iter(|| {
                let mut p = BigNum::new().unwrap();
                p.generate_prime(black_box(bits as i32), false, None, None)
                    .unwrap();
                p
            })
        });
    }
    g.finish();

    // Keys of 2048, 3072 and 4096 bits with `e = 65537`; the ids' size is the
    // modulus' bytes. Like the primes, verified-garbage's key is from fixed
    // octets (`generate(bits, e)` but for `getrandom`): two primes, the key
    // from them, its check, and the pairwise consistency test. So that the
    // draw is a typical one, they are the stream, of the streams of nine
    // fixed seeds, whose key reads the median number of octets. OpenSSL's
    // `RSA_generate_key_ex` draws from its own generator.
    let mut g = c.benchmark_group("rsa_keygen_generate");
    g.sample_size(10);
    for bits in [2048, 3072, 4096] {
        let mut draws: Vec<(usize, Vec<u8>)> = (0..9)
            .map(|i| {
                let rand = fixed_octets(bits + i, |r| generate_from(bits, &[1, 0, 1], r).is_ok());
                (generate_from(bits, &[1, 0, 1], &rand).unwrap().1, rand)
            })
            .collect();
        draws.sort_by_key(|d| d.0);
        let rand = draws.swap_remove(4).1;
        g.bench_function(BenchmarkId::new(VG, bits / 8), |b| {
            b.iter(|| {
                generate_from(black_box(bits), black_box(&[1, 0, 1]), black_box(&rand)).unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, bits / 8), |b| {
            b.iter(|| Rsa::generate(black_box(bits as u32)).unwrap())
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

    // The same sizes: the key from two primes OpenSSL generated and
    // `e = 65537`: `n`, `d = e⁻¹ mod lcm(p - 1, q - 1)` and the CRT values
    // (verified-garbage's with the checks of `RSA_check_key`; OpenSSL's
    // `RSA_check_key` also tests the primes, so OpenSSL only computes the
    // values, with its own arithmetic).
    let mut g = c.benchmark_group("rsa_keygen_key");
    g.sample_size(10);
    for bits in [1024, 1536, 2048] {
        let prime = || {
            let mut p = BigNum::new().unwrap();
            p.generate_prime(bits, false, None, None).unwrap();
            p
        };
        let (mut p, mut q) = (prime(), prime());
        if p < q {
            std::mem::swap(&mut p, &mut q);
        }
        let (pv, qv) = (p.to_vec(), q.to_vec());
        assert!(key_from_primes(&[1, 0, 1], &pv, &qv).unwrap().check_key());
        let mut ctx = BigNumContext::new().unwrap();
        g.bench_function(BenchmarkId::new(VG, bits / 8), |b| {
            b.iter(|| {
                key_from_primes(black_box(&[1, 0, 1]), black_box(&pv), black_box(&qv)).unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, bits / 8), |b| {
            b.iter(|| {
                let one = BigNum::from_u32(1).unwrap();
                let e = BigNum::from_u32(65537).unwrap();
                let (p, q) = (black_box(&p), black_box(&q));
                let mut p1 = BigNum::new().unwrap();
                p1.checked_sub(p, &one).unwrap();
                let mut q1 = BigNum::new().unwrap();
                q1.checked_sub(q, &one).unwrap();
                let mut g = BigNum::new().unwrap();
                g.gcd(&p1, &q1, &mut ctx).unwrap();
                let mut phi = BigNum::new().unwrap();
                phi.checked_mul(&p1, &q1, &mut ctx).unwrap();
                let mut lcm = BigNum::new().unwrap();
                lcm.checked_div(&phi, &g, &mut ctx).unwrap();
                let mut d = BigNum::new().unwrap();
                d.mod_inverse(&e, &lcm, &mut ctx).unwrap();
                let mut dp = BigNum::new().unwrap();
                dp.checked_rem(&d, &p1, &mut ctx).unwrap();
                let mut dq = BigNum::new().unwrap();
                dq.checked_rem(&d, &q1, &mut ctx).unwrap();
                let mut qinv = BigNum::new().unwrap();
                qinv.mod_inverse(q, p, &mut ctx).unwrap();
                let mut n = BigNum::new().unwrap();
                n.checked_mul(p, q, &mut ctx).unwrap();
                Rsa::from_private_components(
                    n,
                    e,
                    d,
                    BigNum::from_slice(&p.to_vec()).unwrap(),
                    BigNum::from_slice(&q.to_vec()).unwrap(),
                    dp,
                    dq,
                    qinv,
                )
                .unwrap()
            })
        });
    }
    g.finish();
}

/// The shortest stream of octets from a splitmix64 generator seeded with
/// `seed`, grown by doubling from `seed / 4` octets, that is `enough`.
#[cfg(target_arch = "x86_64")]
fn fixed_octets(seed: usize, enough: impl Fn(&[u8]) -> bool) -> Vec<u8> {
    let start = seed / 4;
    let mut seed = seed as u64;
    let mut next = || {
        seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let z = (seed ^ (seed >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        let z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    let mut rand: Vec<u8> = Vec::new();
    while !enough(&rand) {
        for _ in 0..(rand.len() / 8).max(start / 8) {
            rand.extend(next().to_le_bytes());
        }
    }
    rand
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
