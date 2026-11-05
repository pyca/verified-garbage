//! The loading of an RSA private key from `(n, e, d, p, q, dP, dQ, qInv)`,
//! from `(n, e, d, p, q)` and from `(n, e, d)`, each checked as BoringSSL's
//! `RSA_check_key` checks a key.

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

    use aws_lc_rs::rsa::KeyPairComponents;
    use aws_lc_rs::signature::{RsaKeyPair, RsaPublicKeyComponents};
    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext, BigNumRef};
    use openssl::pkey::Private;
    use openssl::rsa::Rsa;
    use verified_garbage::rsa::PrivateKey;

    use crate::{AWS_LC, BenchDyn, OPENSSL, VG};

    // OpenSSL has no function that brings `(n, e, d, p, q)` to the CRT form,
    // or that recovers `p` and `q` from `(n, e, d)`: its nearest is the same
    // arithmetic with its `BigNum`s (the CRT values, and SP 800-56B Rev. 2
    // Appendix C.1 with the candidates 2, 3, …, as `from_components` where it
    // does not use Appendix C.2), then `Rsa::from_private_components`.
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
    /// The primes of `(n, e, d)` with the candidates from 2, and the
    /// candidate that found them.
    fn openssl_recover_with(n: &BigNumRef, e: &BigNumRef, d: &BigNumRef) -> (Rsa<Private>, u32) {
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
                    found = Some((y, g));
                    break 'g;
                }
                if x == n1 || j + 1 == t {
                    continue 'g;
                }
                y = x;
            }
        }
        let (mut y1, g) = found.unwrap();
        y1.sub_word(1).unwrap();
        let mut p = BigNum::new().unwrap();
        p.gcd(&y1, n, &mut ctx).unwrap();
        let mut q = BigNum::new().unwrap();
        q.checked_div(n, &p, &mut ctx).unwrap();
        (openssl_crt(n, e, d, &p, &q), g)
    }
    fn openssl_recover(n: &BigNumRef, e: &BigNumRef, d: &BigNumRef) -> Rsa<Private> {
        openssl_recover_with(n, e, d).0
    }

    let mut g = c.benchmark_group("rsa_from_crt");
    // The same sizes: the loading of a key from all its values,
    // `(n, e, d, p, q, dP, dQ, qInv)`, as from a PKCS #1 `RSAPrivateKey`.
    // verified-garbage and aws-lc-rs check the key as they load it (with the
    // checks of BoringSSL's `RSA_check_key`); OpenSSL's
    // `Rsa::from_private_components` checks nothing.
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let v = [
            key.n(),
            key.e(),
            key.d(),
            key.p().unwrap(),
            key.q().unwrap(),
            key.dmp1().unwrap(),
            key.dmq1().unwrap(),
            key.iqmp().unwrap(),
        ]
        .map(|x| x.to_vec());
        let k = v[0].len();
        g.bench(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                let v = black_box(&v);
                PrivateKey::from_crt(&v[0], &v[1], &v[2], &v[3], &v[4], &v[5], &v[6], &v[7])
                    .unwrap()
            })
        });
        g.bench(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                let v = black_box(&v)
                    .clone()
                    .map(|x| BigNum::from_slice(&x).unwrap());
                let [n, e, d, p, q, dp, dq, qinv] = v;
                Rsa::from_private_components(n, e, d, p, q, dp, dq, qinv).unwrap()
            })
        });
        g.bench(BenchmarkId::new(AWS_LC, k), |b| {
            b.iter(|| {
                let v = black_box(&v);
                RsaKeyPair::from_components(&KeyPairComponents {
                    public_key: RsaPublicKeyComponents {
                        n: &v[0][..],
                        e: &v[1][..],
                    },
                    d: &v[2][..],
                    p: &v[3][..],
                    q: &v[4][..],
                    dP: &v[5][..],
                    dQ: &v[6][..],
                    qInv: &v[7][..],
                })
                .unwrap()
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("rsa_from_primes");
    // The same sizes: the CRT values of `(n, e, d, p, q)` and the key.
    for bits in [2048, 3072, 4096] {
        let key = Rsa::generate(bits).unwrap();
        let (n, e, d) = (key.n().to_vec(), key.e().to_vec(), key.d().to_vec());
        let (p, q) = (key.p().unwrap().to_vec(), key.q().unwrap().to_vec());
        let k = n.len();
        g.bench(BenchmarkId::new(VG, k), |b| {
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
        g.bench(BenchmarkId::new(OPENSSL, k), |b| {
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
    // The recovery's time is that of the candidates it tries, so each size
    // takes a key whose first candidate, 2, finds the primes (as most do):
    // the time is then the same for every run's random key.
    for bits in [2048, 3072, 4096] {
        let key = loop {
            let key = Rsa::generate(bits).unwrap();
            if openssl_recover_with(key.n(), key.e(), key.d()).1 == 2 {
                break key;
            }
        };
        let (n, e, d) = (key.n().to_vec(), key.e().to_vec(), key.d().to_vec());
        let k = n.len();
        g.bench(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                PrivateKey::from_components(black_box(&n), black_box(&e), black_box(&d)).unwrap()
            })
        });
        g.bench(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| openssl_recover(black_box(key.n()), black_box(key.e()), black_box(key.d())))
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
