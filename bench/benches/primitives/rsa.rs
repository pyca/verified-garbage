//! The RSA public-key operation (RSAEP) and private-key operation (RSADP with
//! the CRT, checked against the public exponent), without padding, the
//! loading of a private key from `(n, e, d, p, q)` and from `(n, e, d)`, and
//! the check of a private key.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext, BigNumRef};
    use openssl::pkey::Private;
    use openssl::rsa::{Padding, Rsa};
    use verified_garbage::rsa::{PrivateKey, PublicKey};

    use crate::{OPENSSL, VG};
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

    let mut g = c.benchmark_group("rsa_private");
    // The same sizes, each library holding the private key in the CRT form
    // `(p, q, dP, dQ, qInv)` (OpenSSL with its default blinding). Both check
    // the result against `e` (OpenSSL's `rsa_ossl_mod_exp` verifies it too).
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let n = key.n().to_vec();
        let k = n.len();
        let vg_key = PrivateKey::from_crt(
            &n,
            &key.e().to_vec(),
            &key.d().to_vec(),
            &key.p().unwrap().to_vec(),
            &key.q().unwrap().to_vec(),
            &key.dmp1().unwrap().to_vec(),
            &key.dmq1().unwrap().to_vec(),
            &key.iqmp().unwrap().to_vec(),
        )
        .unwrap();
        let mut input = vec![0x42; k];
        input[0] = 0;
        let mut out = vec![0; k];
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                black_box(&vg_key)
                    .private_op(black_box(&input), &mut out)
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                black_box(&key)
                    .private_decrypt(black_box(&input), &mut out, Padding::NONE)
                    .unwrap()
            })
        });
    }
    g.finish();

    // OpenSSL has no function that brings `(n, e, d, p, q)` to the CRT form,
    // or that recovers `p` and `q` from `(n, e, d)`: its nearest is the same
    // arithmetic with its `BigNum`s (the CRT values, and SP 800-56B Rev. 2
    // Appendix C.1 with the candidates 2, 3, …, as `from_components`), then
    // `Rsa::from_private_components`.
    fn openssl_crt(
        n: &BigNumRef,
        e: &BigNumRef,
        d: &BigNumRef,
        p: &BigNumRef,
        q: &BigNumRef,
    ) -> Rsa<Private> {
        let mut ctx = BigNumContext::new().unwrap();
        let mut p1 = p.to_owned().unwrap();
        p1.sub_word(1).unwrap();
        let mut q1 = q.to_owned().unwrap();
        q1.sub_word(1).unwrap();
        let (mut dp, mut dq, mut qinv) = (
            BigNum::new().unwrap(),
            BigNum::new().unwrap(),
            BigNum::new().unwrap(),
        );
        dp.nnmod(d, &p1, &mut ctx).unwrap();
        dq.nnmod(d, &q1, &mut ctx).unwrap();
        qinv.mod_inverse(q, p, &mut ctx).unwrap();
        Rsa::from_private_components(
            n.to_owned().unwrap(),
            e.to_owned().unwrap(),
            d.to_owned().unwrap(),
            p.to_owned().unwrap(),
            q.to_owned().unwrap(),
            dp,
            dq,
            qinv,
        )
        .unwrap()
    }
    fn openssl_recover(n: &BigNumRef, e: &BigNumRef, d: &BigNumRef) -> Rsa<Private> {
        let mut ctx = BigNumContext::new().unwrap();
        let mut r = BigNum::new().unwrap();
        r.checked_mul(d, e, &mut ctx).unwrap();
        r.sub_word(1).unwrap();
        let mut t = 0;
        while r.is_even() {
            let x = r.to_owned().unwrap();
            r.rshift1(&x).unwrap();
            t += 1;
        }
        let mut n1 = n.to_owned().unwrap();
        n1.sub_word(1).unwrap();
        let one = BigNum::from_u32(1).unwrap();
        let mut found = None;
        'g: for g in 2..102 {
            let mut y = BigNum::new().unwrap();
            y.mod_exp(&BigNum::from_u32(g).unwrap(), &r, n, &mut ctx)
                .unwrap();
            if y == one || y == n1 {
                continue;
            }
            for j in 0..t {
                let mut x = BigNum::new().unwrap();
                x.mod_sqr(&y, n, &mut ctx).unwrap();
                if x == one {
                    found = Some(y);
                    break 'g;
                }
                if x == n1 || j + 1 == t {
                    continue 'g;
                }
                y = x;
            }
        }
        let mut y1 = found.unwrap();
        y1.sub_word(1).unwrap();
        let mut p = BigNum::new().unwrap();
        p.gcd(&y1, n, &mut ctx).unwrap();
        let mut q = BigNum::new().unwrap();
        q.checked_div(n, &p, &mut ctx).unwrap();
        openssl_crt(n, e, d, &p, &q)
    }

    let mut g = c.benchmark_group("rsa_from_primes");
    // The same sizes: the CRT values of `(n, e, d, p, q)` and the key.
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e, d) = (key.n().to_vec(), key.e().to_vec(), key.d().to_vec());
        let (p, q) = (key.p().unwrap().to_vec(), key.q().unwrap().to_vec());
        let k = n.len();
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                PrivateKey::from_primes(
                    black_box(&n),
                    black_box(&e),
                    black_box(&d),
                    black_box(&p),
                    black_box(&q),
                )
                .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                openssl_crt(
                    black_box(key.n()),
                    black_box(key.e()),
                    black_box(key.d()),
                    black_box(key.p().unwrap()),
                    black_box(key.q().unwrap()),
                )
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("rsa_from_components");
    // The same sizes: the primes of `(n, e, d)`, their CRT values and the key.
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e, d) = (key.n().to_vec(), key.e().to_vec(), key.d().to_vec());
        let k = n.len();
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                PrivateKey::from_components(black_box(&n), black_box(&e), black_box(&d)).unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| openssl_recover(black_box(key.n()), black_box(key.e()), black_box(key.d())))
        });
    }
    g.finish();

    let mut g = c.benchmark_group("rsa_check_key");
    // The same sizes: each library's `RSA_check_key` of a key it holds.
    // OpenSSL's also tests `p` and `q` for primality, which BoringSSL's (and
    // `check_key`) does not.
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let n = key.n().to_vec();
        let k = n.len();
        let vg_key = PrivateKey::from_crt(
            &n,
            &key.e().to_vec(),
            &key.d().to_vec(),
            &key.p().unwrap().to_vec(),
            &key.q().unwrap().to_vec(),
            &key.dmp1().unwrap().to_vec(),
            &key.dmq1().unwrap().to_vec(),
            &key.iqmp().unwrap().to_vec(),
        )
        .unwrap();
        g.bench_function(BenchmarkId::new(VG, k), |b| {
            b.iter(|| assert!(black_box(&vg_key).check_key()))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| assert!(black_box(&key).check_key().unwrap()))
        });
    }
    g.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
