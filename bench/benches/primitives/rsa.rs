//! The RSA private-key operation (RSADP with the CRT, checked against the
//! public exponent), without padding, the loading of a private key from
//! `(n, e, d, p, q, dP, dQ, qInv)`, from `(n, e, d, p, q)` and from
//! `(n, e, d)`, and the check of a private key (the public-key operation is
//! `rsa_public`).

use criterion::Criterion;

pub const USES: &[&str] = &["rsa"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::BenchmarkId;
    use openssl::rsa::{Padding, Rsa};
    use verified_garbage::rsa::PrivateKey;

    use crate::{BenchDyn, OPENSSL, VG};
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
        g.bench(BenchmarkId::new(VG, k), |b| {
            b.iter(|| {
                black_box(&vg_key)
                    .private_op(black_box(&input), &mut out)
                    .unwrap()
            })
        });
        g.bench(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| {
                black_box(&key)
                    .private_decrypt(black_box(&input), &mut out, Padding::NONE)
                    .unwrap()
            })
        });
    }
    g.finish();

    keys(c);
}

/// The loading of a private key from `(n, e, d, p, q, dP, dQ, qInv)`, from
/// `(n, e, d, p, q)` and from `(n, e, d)`, and the check of a private key.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64"
))]
fn keys(c: &mut Criterion) {
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
    // aws-lc-rs checks the key as it loads it; OpenSSL's
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
        g.bench(BenchmarkId::new(VG, k), |b| {
            b.iter(|| assert!(black_box(&vg_key).check_key()))
        });
        g.bench(BenchmarkId::new(OPENSSL, k), |b| {
            b.iter(|| assert!(black_box(&key).check_key().unwrap()))
        });
    }
    g.finish();
}

#[cfg(target_arch = "riscv64")]
pub fn bench(c: &mut Criterion) {
    // Prototype (bench branch only): unproven Montgomery multiplication and
    // squaring of `w` words, next to OpenSSL's `BN_mod_mul`, `BN_mod_sqr`,
    // and `BN_mod_exp` of an exponent as long as the modulus (a CRT half), for
    // which the prototype does one squaring per bit and one multiplication
    // per four bits (a 4-bit window).
    use criterion::BenchmarkId;
    use openssl::bn::{BigNum, BigNumContext};
    use std::hint::black_box;
    use verified_garbage_asm_riscv64::rsa_proto::{vg_proto_mont_mul, vg_proto_mont_sqr};

    use crate::{OPENSSL, VG};
    {
        // The unproven private-key operation (CRT, checked against e), next to OpenSSL's.
        use openssl::rsa::{Padding, Rsa};
        use verified_garbage_asm_riscv64::rsa_proto2::vg_rsa_private_checked;
        let mut g = c.benchmark_group("rsa_proto_private");
        for bits in [2048u32, 3072, 4096] {
            let key = Rsa::generate(bits).unwrap();
            let k = key.size() as usize;
            let pad = |b: Vec<u8>, l: usize| {
                let mut v = vec![0u8; l - b.len()];
                v.extend(b);
                v
            };
            let (n, e) = (key.n().to_vec(), key.e().to_vec());
            let (p, q) = (key.p().unwrap().to_vec(), key.q().unwrap().to_vec());
            let (pl, ql) = (p.len(), q.len());
            let dp = pad(key.dmp1().unwrap().to_vec(), pl);
            let dq = pad(key.dmq1().unwrap().to_vec(), ql);
            let qi = pad(key.iqmp().unwrap().to_vec(), pl);
            let mut input = vec![0x42; k];
            input[0] = 0;
            let mut out = vec![0; k];
            let mut scratch = vec![0u64; 16 * k + 64];
            g.bench_function(BenchmarkId::new(VG, bits), |b| {
                b.iter(|| unsafe {
                    vg_rsa_private_checked(
                        out.as_mut_ptr(),
                        k,
                        n.as_ptr(),
                        k,
                        e.as_ptr(),
                        e.len(),
                        black_box(input.as_ptr()),
                        k,
                        p.as_ptr(),
                        pl,
                        q.as_ptr(),
                        ql,
                        dp.as_ptr(),
                        pl,
                        dq.as_ptr(),
                        ql,
                        qi.as_ptr(),
                        pl,
                        scratch.as_mut_ptr(),
                        scratch.len(),
                    )
                })
            });
            g.bench_function(BenchmarkId::new(OPENSSL, bits), |b| {
                b.iter(|| {
                    key.private_decrypt(black_box(&input), &mut out, Padding::NONE)
                        .unwrap()
                })
            });
        }
        g.finish();
    }
    {
        // The unproven recovery of the primes by SP 800-56B's Appendix C.2.
        {
            use verified_garbage_asm_riscv64::rsa_proto4::vg_rsa_recover_primes_det;
            let mut g = c.benchmark_group("rsa_proto_recover_det");
            for bits in [2048u32, 3072, 4096] {
                let key = openssl::rsa::Rsa::generate(bits).unwrap();
                let k = key.size() as usize;
                let (n, e, d) = (key.n().to_vec(), key.e().to_vec(), key.d().to_vec());
                let (mut p, mut q) = (vec![0u8; k], vec![0u8; k]);
                let mut scratch = vec![0u64; 16 * k + 32];
                g.bench_function(BenchmarkId::new(VG, bits), |b| {
                    b.iter(|| unsafe {
                        vg_rsa_recover_primes_det(
                            p.as_mut_ptr(),
                            k,
                            q.as_mut_ptr(),
                            k,
                            n.as_ptr(),
                            k,
                            e.as_ptr(),
                            e.len(),
                            black_box(d.as_ptr()),
                            d.len(),
                            scratch.as_mut_ptr(),
                            scratch.len(),
                        )
                    })
                });
            }
            g.finish();
        }
        // The unproven key functions: the CRT values, and the two key checks (next to OpenSSL's RSA_check_key).
        use openssl::rsa::Rsa;
        use verified_garbage_asm_riscv64::rsa_proto3::{
            vg_rsa_check_crt_key, vg_rsa_check_key, vg_rsa_crt_values,
        };
        for (name, kind) in [
            ("rsa_proto_crt_values", 0),
            ("rsa_proto_check_key", 1),
            ("rsa_proto_check_crt_key", 2),
        ] {
            let mut g = c.benchmark_group(name);
            for bits in [2048u32, 4096] {
                let key = Rsa::generate(bits).unwrap();
                let k = key.size() as usize;
                let pad = |b: Vec<u8>, l: usize| {
                    let mut v = vec![0u8; l - b.len()];
                    v.extend(b);
                    v
                };
                let (n, e, d) = (key.n().to_vec(), key.e().to_vec(), pad(key.d().to_vec(), k));
                let (p, q) = (key.p().unwrap().to_vec(), key.q().unwrap().to_vec());
                let (pl, ql) = (p.len(), q.len());
                let dp = pad(key.dmp1().unwrap().to_vec(), pl);
                let dq = pad(key.dmq1().unwrap().to_vec(), ql);
                let qi = pad(key.iqmp().unwrap().to_vec(), pl);
                let mut scratch = vec![0u64; 16 * k + 64];
                let (mut odp, mut odq, mut oqi) = (vec![0u8; pl], vec![0u8; ql], vec![0u8; pl]);
                g.bench_function(BenchmarkId::new(VG, bits), |b| match kind {
                    0 => b.iter(|| unsafe {
                        vg_rsa_crt_values(
                            odp.as_mut_ptr(),
                            pl,
                            odq.as_mut_ptr(),
                            ql,
                            oqi.as_mut_ptr(),
                            pl,
                            n.as_ptr(),
                            k,
                            p.as_ptr(),
                            pl,
                            q.as_ptr(),
                            ql,
                            black_box(d.as_ptr()),
                            k,
                            scratch.as_mut_ptr(),
                            scratch.len(),
                        )
                    }),
                    1 => b.iter(|| unsafe {
                        vg_rsa_check_key(
                            n.as_ptr(),
                            k,
                            e.as_ptr(),
                            e.len(),
                            black_box(d.as_ptr()),
                            k,
                            p.as_ptr(),
                            pl,
                            q.as_ptr(),
                            ql,
                            dp.as_ptr(),
                            pl,
                            dq.as_ptr(),
                            ql,
                            qi.as_ptr(),
                            pl,
                            scratch.as_mut_ptr(),
                            scratch.len(),
                        )
                    }),
                    _ => b.iter(|| unsafe {
                        vg_rsa_check_crt_key(
                            n.as_ptr(),
                            k,
                            e.as_ptr(),
                            e.len(),
                            black_box(p.as_ptr()),
                            pl,
                            q.as_ptr(),
                            ql,
                            dp.as_ptr(),
                            pl,
                            dq.as_ptr(),
                            ql,
                            qi.as_ptr(),
                            pl,
                            scratch.as_mut_ptr(),
                            scratch.len(),
                        )
                    }),
                });
                if kind == 1 {
                    g.bench_function(BenchmarkId::new(OPENSSL, bits), |b| {
                        b.iter(|| black_box(&key).check_key().unwrap())
                    });
                }
            }
            g.finish();
        }
    }
    let mut ctx = BigNumContext::new().unwrap();
    for (name, kind) in [
        ("rsa_proto_mul", 0),
        ("rsa_proto_sqr", 1),
        ("rsa_proto_exp", 2),
    ] {
        let mut g = c.benchmark_group(name);
        for w in [16usize, 24, 32, 48, 64] {
            let bits = 64 * w as i32;
            let mut ws = vec![0u64; 32 + 8 * (w + 2)];
            for (i, x) in ws.iter_mut().enumerate().skip(32) {
                *x = (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
            }
            ws[32] |= 1;
            g.bench_function(BenchmarkId::new(VG, bits), |b| match kind {
                0 => b.iter(|| unsafe { vg_proto_mont_mul(black_box(ws.as_mut_ptr()), w, 1) }),
                1 => b.iter(|| unsafe { vg_proto_mont_sqr(black_box(ws.as_mut_ptr()), w, 1) }),
                _ => b.iter(|| unsafe {
                    vg_proto_mont_sqr(black_box(ws.as_mut_ptr()), w, 64 * w);
                    vg_proto_mont_mul(black_box(ws.as_mut_ptr()), w, 16 * w);
                }),
            });
            let mut m = BigNum::new().unwrap();
            m.rand(bits, openssl::bn::MsbOption::ONE, true).unwrap();
            let mut a = BigNum::new().unwrap();
            m.rand_range(&mut a).unwrap();
            let mut e = BigNum::new().unwrap();
            e.rand(bits, openssl::bn::MsbOption::ONE, true).unwrap();
            let mut r = BigNum::new().unwrap();
            g.bench_function(BenchmarkId::new(OPENSSL, bits), |b| match kind {
                0 => b.iter(|| r.mod_mul(black_box(&a), &a, &m, &mut ctx).unwrap()),
                1 => b.iter(|| r.mod_sqr(black_box(&a), &m, &mut ctx).unwrap()),
                _ => b.iter(|| r.mod_exp(black_box(&a), &e, &m, &mut ctx).unwrap()),
            });
        }
        g.finish();
    }
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
