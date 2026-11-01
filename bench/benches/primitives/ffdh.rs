//! FFDH component operations against OpenSSL and AWS-LC.
// AWS-LC's C DH API is in aws-lc-sys's full bindings, which the benchmarks
// build only on x86-64 and AArch64; aws-lc-rs exposes no DH wrapper. ARMv7,
// i686 and PPC64LE compare with OpenSSL.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
#[path = "../../support/ffdh.rs"]
mod aws_lc;
use criterion::Criterion;
pub const USES: &[&str] = &["ffdh", "rsa_mont", "miller_rabin"];
#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    use crate::AWS_LC;
    use crate::{OPENSSL, VG, fixed_tape};
    use criterion::BenchmarkId;
    use openssl::{bn::BigNum, derive::Deriver, dh::Dh, pkey::PKey, pkey_ctx::PkeyCtx};
    use std::hint::black_box;
    use verified_garbage::ffdh::{Parameters, PrivateKey, PublicKey};
    for size in [2048, 3072, 4096] {
        let dh = match size {
            2048 => Dh::get_2048_256().unwrap(),
            3072 => Dh::from_pqg(
                BigNum::get_rfc3526_prime_3072().unwrap(),
                None,
                BigNum::from_u32(2).unwrap(),
            )
            .unwrap(),
            _ => Dh::from_pqg(
                BigNum::get_rfc3526_prime_4096().unwrap(),
                None,
                BigNum::from_u32(2).unwrap(),
            )
            .unwrap(),
        };
        let (p, g, q) = (
            dh.prime_p().to_vec(),
            dh.generator().to_vec(),
            dh.prime_q().map(|q| q.to_vec()),
        );
        let params = Parameters::from_components(&p, &g, q.as_deref()).unwrap();
        let openssl_key = dh.generate_key().unwrap();
        let (x, y) = (
            openssl_key.private_key().to_vec(),
            openssl_key.public_key().to_vec(),
        );
        let openssl_pkey = PKey::from_dh(openssl_key).unwrap();
        let openssl_key = openssl_pkey.dh().unwrap();
        let key = PrivateKey::from_components(&params, &y, &x).unwrap();
        let peer = params.generate_private_key().unwrap();
        let openssl_peer = PKey::from_dh(
            Dh::from_pqg(
                BigNum::from_slice(&p).unwrap(),
                q.as_ref().map(|q| BigNum::from_slice(q).unwrap()),
                BigNum::from_slice(&g).unwrap(),
            )
            .unwrap()
            .set_public_key(BigNum::from_slice(peer.public_key().component()).unwrap())
            .unwrap(),
        )
        .unwrap();
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        let aws_key = aws_lc::Dh::parameters(&p, &g, q.as_deref()).with_key(&y, &x);
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        let aws_peer = aws_lc::Dh::parameters(&p, &g, q.as_deref())
            .with_key(peer.public_key().component(), peer.private_component());
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        assert_eq!(
            aws_key.exchange(&aws_peer),
            key.exchange(peer.public_key()).unwrap()
        );
        // OpenSSL's compute_key strips leading zero bytes; pad explicitly
        // to compare the complete operation cryptography needs.
        let mut group = c.benchmark_group("ffdh_exchange");
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        group.bench_function(BenchmarkId::new(AWS_LC, size / 8), |b| {
            b.iter(|| black_box(&aws_key).exchange(black_box(&aws_peer)))
        });
        group.bench_function(BenchmarkId::new(VG, size / 8), |b| {
            b.iter(|| {
                black_box(&key)
                    .exchange(black_box(peer.public_key()))
                    .unwrap()
            })
        });
        group.bench_function(BenchmarkId::new(OPENSSL, size / 8), |b| {
            b.iter(|| {
                let mut deriver = Deriver::new(&openssl_pkey).unwrap();
                deriver.set_peer(black_box(&openssl_peer)).unwrap();
                let z = deriver.derive_to_vec().unwrap();
                let mut out = vec![0; p.len()];
                let offset = out.len() - z.len();
                out[offset..].copy_from_slice(&z);
                black_box(out)
            })
        });
        group.finish();
        // Cold checked construction.
        // VG validates imported parameters; OpenSSL only constructs its object.
        let mut group = c.benchmark_group("ffdh_parameters_from");
        group.bench_function(BenchmarkId::new(VG, size / 8), |b| {
            b.iter(|| {
                Parameters::from_components(black_box(&p), black_box(&g), q.as_deref()).unwrap()
            })
        });
        group.bench_function(BenchmarkId::new(OPENSSL, size / 8), |b| {
            b.iter(|| {
                Dh::from_pqg(
                    BigNum::from_slice(black_box(&p)).unwrap(),
                    q.as_ref().map(|q| BigNum::from_slice(q).unwrap()),
                    BigNum::from_slice(black_box(&g)).unwrap(),
                )
                .unwrap()
            })
        });
        group.finish();
        let mut group = c.benchmark_group("ffdh_from_private");
        group.bench_function(BenchmarkId::new(VG, size / 8), |b| {
            b.iter(|| {
                PrivateKey::from_private_components(black_box(&params), black_box(&x)).unwrap()
            })
        });
        group.bench_function(BenchmarkId::new(OPENSSL, size / 8), |b| {
            b.iter(|| {
                Dh::from_pqg(
                    BigNum::from_slice(black_box(&p)).unwrap(),
                    q.as_ref().map(|q| BigNum::from_slice(q).unwrap()),
                    BigNum::from_slice(black_box(&g)).unwrap(),
                )
                .unwrap()
                .set_private_key(BigNum::from_slice(black_box(&x)).unwrap())
                .unwrap()
            })
        });
        group.finish();
        // Cold cases include the checked constructor. Keep these separate
        // from reused-Parameters generation below: one-key total cost can
        // dominate warm gains.
        // Here and below, verified-garbage draws its keys from a fixed tape
        // (`generate_private_key` but for `getrandom`); OpenSSL and AWS-LC
        // draw from their own generators.
        let mut group = c.benchmark_group("ffdh_cold_first_key");
        group.bench_function(BenchmarkId::new(VG, size / 8), |b| {
            b.iter(|| {
                let mut tape = fixed_tape(size as u64);
                Parameters::from_components(black_box(&p), black_box(&g), q.as_deref())
                    .unwrap()
                    .generate_private_key_with_rng(|buf: &mut [u8]| {
                        tape(buf);
                        Ok::<_, ()>(())
                    })
                    .unwrap()
            })
        });
        group.bench_function(BenchmarkId::new(OPENSSL, size / 8), |b| {
            b.iter(|| {
                Dh::from_pqg(
                    BigNum::from_slice(black_box(&p)).unwrap(),
                    q.as_ref().map(|q| BigNum::from_slice(q).unwrap()),
                    BigNum::from_slice(black_box(&g)).unwrap(),
                )
                .unwrap()
                .generate_key()
                .unwrap()
            })
        });
        group.finish();
        // Reuse the public parameter object and initialized keygen context
        // for OpenSSL as well; neither warm case reconstructs p/q/g.
        let openssl_params = PKey::from_dh(
            Dh::from_pqg(
                BigNum::from_slice(&p).unwrap(),
                q.as_ref().map(|q| BigNum::from_slice(q).unwrap()),
                BigNum::from_slice(&g).unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
        // Warm: params already exists.
        let mut group = c.benchmark_group("ffdh_generate");
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        group.bench_function(BenchmarkId::new(AWS_LC, size / 8), |b| {
            b.iter(|| aws_lc::Dh::parameters(&p, &g, q.as_deref()).generate())
        });
        group.bench_function(BenchmarkId::new(VG, size / 8), |b| {
            b.iter(|| {
                let mut tape = fixed_tape(size as u64);
                black_box(&params)
                    .generate_private_key_with_rng(|buf: &mut [u8]| {
                        tape(buf);
                        Ok::<_, ()>(())
                    })
                    .unwrap()
            })
        });
        group.bench_function(BenchmarkId::new(OPENSSL, size / 8), |b| {
            let mut keygen = PkeyCtx::new(&openssl_params).unwrap();
            keygen.keygen_init().unwrap();
            b.iter(|| keygen.keygen().unwrap())
        });
        group.finish();
        let mut group = c.benchmark_group("ffdh_private_from");
        group.bench_function(BenchmarkId::new(VG, size / 8), |b| {
            b.iter(|| {
                PrivateKey::from_components(black_box(&params), black_box(&y), black_box(&x))
                    .unwrap()
            })
        });
        group.bench_function(BenchmarkId::new(OPENSSL, size / 8), |b| {
            b.iter(|| {
                Dh::from_pqg(
                    BigNum::from_slice(&p).unwrap(),
                    q.as_ref().map(|q| BigNum::from_slice(q).unwrap()),
                    BigNum::from_slice(&g).unwrap(),
                )
                .unwrap()
                .set_key(
                    BigNum::from_slice(&y).unwrap(),
                    BigNum::from_slice(&x).unwrap(),
                )
                .unwrap()
            })
        });
        group.finish();
        let mut group = c.benchmark_group("ffdh_public_from");
        group.bench_function(BenchmarkId::new(VG, size / 8), |b| {
            b.iter(|| PublicKey::from_components(black_box(&params), black_box(&y)).unwrap())
        });
        group.bench_function(BenchmarkId::new(OPENSSL, size / 8), |b| {
            b.iter(|| {
                Dh::from_pqg(
                    BigNum::from_slice(&p).unwrap(),
                    q.as_ref().map(|q| BigNum::from_slice(q).unwrap()),
                    BigNum::from_slice(&g).unwrap(),
                )
                .unwrap()
                .set_public_key(BigNum::from_slice(&y).unwrap())
                .unwrap()
            })
        });
        group.finish();
        let mut group = c.benchmark_group("ffdh_components");
        group.bench_function(BenchmarkId::new(VG, size / 8), |b| {
            b.iter(|| {
                black_box(params.components());
                black_box(key.public_key());
                black_box(key.private_component());
                black_box(key.public_key().component());
                black_box(key.public_key().parameters());
                black_box(params.key_size());
            })
        });
        group.bench_function(BenchmarkId::new(OPENSSL, size / 8), |b| {
            b.iter(|| {
                black_box(openssl_key.prime_p());
                black_box(openssl_key.generator());
                black_box(openssl_key.prime_q());
                black_box(openssl_key.public_key());
                black_box(openssl_key.private_key());
                black_box(openssl_key.prime_p().num_bits());
            })
        });
        group.finish();
    }
    // verified-garbage searches from a fixed tape (`generate` but for
    // `getrandom`), so it tests the same candidates and witnesses in every
    // iteration. OpenSSL cannot be given its draws, and draws from its own
    // generator.
    for generator in [2, 5] {
        let mut group = c.benchmark_group(format!("ffdh_parameters_g{generator}"));
        for bits in [
            512,
            #[cfg(target_arch = "arm")]
            1024,
        ] {
            if bits == 1024 && generator != 2 {
                continue;
            }
            // OpenSSL's safe-prime search has high variance: 100 samples at
            // 512 bits; the larger ARM case uses 64 to stay within the
            // native job's time limit.
            group.sample_size(if bits == 512 { 100 } else { 64 });
            group.bench_function(BenchmarkId::new(VG, bits / 8), |b| {
                b.iter(|| {
                    let mut tape = fixed_tape(u64::from(generator));
                    Parameters::generate_with_rng(black_box(bits), generator, |buf: &mut [u8]| {
                        tape(buf);
                        Ok::<_, ()>(())
                    })
                    .unwrap()
                })
            });
            group.bench_function(BenchmarkId::new(OPENSSL, bits / 8), |b| {
                b.iter(|| Dh::generate_params(bits as u32, generator).unwrap())
            });
        }
        group.finish();
    }
}
#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_c: &mut Criterion) {}
