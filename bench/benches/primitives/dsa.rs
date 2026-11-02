//! DSA key generation and prehashed DSA at every supported width, beside
//! OpenSSL's equivalent. aws-lc-rs does not expose a DSA API.
use criterion::Criterion;

pub const USES: &[&str] = &["dsa", "rsa_mont"];

#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
#[path = "../../../tests/cavp/dsa_vectors.rs"]
mod vectors;

#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
#[path = "../../../tests/dsa_legacy.rs"]
mod legacy_vectors;

#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    use crate::{BenchDyn, OPENSSL, VG, fixed_tape};
    use criterion::BenchmarkId;
    use openssl::{
        bn::BigNum,
        dsa::{Dsa, DsaSig},
        pkey::PKey,
        pkey_ctx::PkeyCtx,
    };
    use std::hint::black_box;
    use vectors::{hex, vectors};
    use verified_garbage::dsa::{PrivateKey, PublicKey};

    let cases = vectors(
        include_str!("../../../vectors/nist-cavp-dsa/SigGen.txt"),
        true,
    );
    for (p_len, q_len) in [(128, 20), (256, 20), (256, 28), (256, 32), (384, 32)] {
        let (p, q, g, y, x) = if (p_len, q_len) == (256, 20) {
            let (p, q, g) = legacy_vectors::parameters();
            let mut x = vec![0; q_len];
            x[q_len - 1] = 1;
            (p, q, g.clone(), g, x)
        } else {
            let v = cases
                .iter()
                .find(|v| hex(&v["P"], 0).len() == p_len && hex(&v["Q"], 0).len() == q_len)
                .unwrap();
            (
                hex(&v["P"], p_len),
                hex(&v["Q"], q_len),
                hex(&v["G"], p_len),
                hex(&v["Y"], p_len),
                hex(&v["X"], q_len),
            )
        };
        let key = PrivateKey::from_components(&p, &q, &g, &y, &x).unwrap();
        let ssl_key = PKey::from_dsa(
            Dsa::from_private_components(
                BigNum::from_slice(&p).unwrap(),
                BigNum::from_slice(&q).unwrap(),
                BigNum::from_slice(&g).unwrap(),
                BigNum::from_slice(&x).unwrap(),
                BigNum::from_slice(&y).unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
        let digest = [0x42; 32];
        // The signature the verification benchmarks check, the same in
        // every run.
        let mut tape = fixed_tape((p_len * 8) as u64);
        let signature = key
            .sign_with_rng(&digest, |buf| {
                tape(buf);
                Ok(())
            })
            .unwrap();
        let der = DsaSig::from_private_components(
            BigNum::from_slice(&signature[..q_len]).unwrap(),
            BigNum::from_slice(&signature[q_len..]).unwrap(),
        )
        .unwrap()
        .to_der()
        .unwrap();
        let mut verify = PkeyCtx::new(&ssl_key).unwrap();
        verify.verify_init().unwrap();
        assert!(verify.verify(&digest, &der).unwrap());
        let mut sign = PkeyCtx::new(&ssl_key).unwrap();
        sign.sign_init().unwrap();
        let mut ssl_sig = Vec::new();
        sign.sign_to_vec(&digest, &mut ssl_sig).unwrap();
        let ssl_sig = DsaSig::from_der(&ssl_sig).unwrap();
        let fixed = [
            ssl_sig.r().to_vec_padded(q_len as i32).unwrap(),
            ssl_sig.s().to_vec_padded(q_len as i32).unwrap(),
        ]
        .concat();
        assert!(key.public_key().verify(&digest, &fixed));
        // CI interprets the final benchmark ID component as a numeric size.
        let size = p_len * 8;

        {
            let mut group = c.benchmark_group(format!("dsa_from_private_q{}", q_len * 8));
            group.bench(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    PrivateKey::from_private_components(
                        black_box(&p),
                        black_box(&q),
                        black_box(&g),
                        black_box(&x),
                    )
                    .unwrap()
                })
            });
            group.bench(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let p = BigNum::from_slice(black_box(&p)).unwrap();
                    let q = BigNum::from_slice(black_box(&q)).unwrap();
                    let g = BigNum::from_slice(black_box(&g)).unwrap();
                    let mut x = BigNum::from_slice(black_box(&x)).unwrap();
                    x.set_const_time();
                    let mut y = BigNum::new().unwrap();
                    let mut ctx = openssl::bn::BigNumContext::new().unwrap();
                    y.mod_exp(&g, &x, &p, &mut ctx).unwrap();
                    Dsa::from_private_components(p, q, g, x, y).unwrap()
                })
            });
            group.finish();
        }

        // verified-garbage draws its nonces and keys below from a fixed tape
        // (`sign` and `generate` but for `getrandom`); OpenSSL draws from
        // its own generator.
        let mut group = c.benchmark_group(format!("dsa_sign_q{}", q_len * 8));
        group.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut tape = fixed_tape(size as u64);
                black_box(&key)
                    .sign_with_rng(black_box(&digest), |buf| {
                        tape(buf);
                        Ok(())
                    })
                    .unwrap()
            })
        });
        group.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut ctx = PkeyCtx::new(black_box(&ssl_key)).unwrap();
                ctx.sign_init().unwrap();
                let mut signature = Vec::new();
                ctx.sign_to_vec(black_box(&digest), &mut signature).unwrap();
                black_box(signature)
            })
        });
        group.finish();
        let mut group = c.benchmark_group(format!("dsa_verify_q{}", q_len * 8));
        group.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| black_box(key.public_key()).verify(black_box(&digest), black_box(&signature)))
        });
        group.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut ctx = PkeyCtx::new(black_box(&ssl_key)).unwrap();
                ctx.verify_init().unwrap();
                ctx.verify(black_box(&digest), black_box(&der)).unwrap()
            })
        });
        group.finish();
        // Import plus the first verification exposes the cost of lazy validation.
        let mut group = c.benchmark_group(format!("dsa_verify_cold_q{}", q_len * 8));
        group.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let fresh = PublicKey::from_components(
                    black_box(&p),
                    black_box(&q),
                    black_box(&g),
                    black_box(&y),
                )
                .unwrap();
                fresh.verify(black_box(&digest), black_box(&signature))
            })
        });
        group.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let key = PKey::from_dsa(
                    Dsa::from_public_components(
                        BigNum::from_slice(black_box(&p)).unwrap(),
                        BigNum::from_slice(black_box(&q)).unwrap(),
                        BigNum::from_slice(black_box(&g)).unwrap(),
                        BigNum::from_slice(black_box(&y)).unwrap(),
                    )
                    .unwrap(),
                )
                .unwrap();
                let mut ctx = PkeyCtx::new(&key).unwrap();
                ctx.verify_init().unwrap();
                ctx.verify(black_box(&digest), black_box(&der)).unwrap()
            })
        });
        group.finish();
        let mut group = c.benchmark_group(format!("dsa_public_key_q{}", q_len * 8));
        group.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                PublicKey::from_components(
                    black_box(&p),
                    black_box(&q),
                    black_box(&g),
                    black_box(&y),
                )
                .unwrap()
            })
        });
        group.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                Dsa::from_public_components(
                    BigNum::from_slice(black_box(&p)).unwrap(),
                    BigNum::from_slice(black_box(&q)).unwrap(),
                    BigNum::from_slice(black_box(&g)).unwrap(),
                    BigNum::from_slice(black_box(&y)).unwrap(),
                )
                .unwrap()
            })
        });
        group.finish();
        let mut group = c.benchmark_group(format!("dsa_private_key_q{}", q_len * 8));
        group.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                PrivateKey::from_components(
                    black_box(&p),
                    black_box(&q),
                    black_box(&g),
                    black_box(&y),
                    black_box(&x),
                )
                .unwrap()
            })
        });
        group.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                Dsa::from_private_components(
                    BigNum::from_slice(black_box(&p)).unwrap(),
                    BigNum::from_slice(black_box(&q)).unwrap(),
                    BigNum::from_slice(black_box(&g)).unwrap(),
                    BigNum::from_slice(black_box(&x)).unwrap(),
                    BigNum::from_slice(black_box(&y)).unwrap(),
                )
                .unwrap()
            })
        });
        group.finish();
        {
            let mut group = c.benchmark_group(format!("dsa_generate_key_q{}", q_len * 8));
            group.bench(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    let mut tape = fixed_tape(size as u64);
                    PrivateKey::generate_with_rng(
                        black_box(&p),
                        black_box(&q),
                        black_box(&g),
                        |buf| {
                            tape(buf);
                            Ok(())
                        },
                    )
                    .unwrap()
                })
            });
            group.bench(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    Dsa::from_pqg(
                        BigNum::from_slice(black_box(&p)).unwrap(),
                        BigNum::from_slice(black_box(&q)).unwrap(),
                        BigNum::from_slice(black_box(&g)).unwrap(),
                    )
                    .unwrap()
                    .generate_key()
                    .unwrap()
                })
            });
            group.finish();
        }
    }
}

#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}
