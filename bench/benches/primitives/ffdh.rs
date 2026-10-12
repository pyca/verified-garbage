//! FFDH component operations against OpenSSL. aws-lc-rs has no FFDH API.
use criterion::Criterion;
pub const USES: &[&str] = &["ffdh", "rsa_mont"];
#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use crate::{OPENSSL, VG};
    use criterion::BenchmarkId;
    use openssl::{bn::BigNum, derive::Deriver, dh::Dh, pkey::PKey};
    use std::hint::black_box;
    use verified_garbage::ffdh::{Parameters, PrivateKey, PublicKey};
    let mut group = c.benchmark_group("ffdh");
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
        // OpenSSL's compute_key strips leading zero bytes; pad explicitly
        // to compare the complete operation cryptography needs.
        group.bench_function(BenchmarkId::new(format!("{VG}/exchange"), size / 8), |b| {
            b.iter(|| {
                black_box(&key)
                    .exchange(black_box(peer.public_key()))
                    .unwrap()
            })
        });
        group.bench_function(
            BenchmarkId::new(format!("{OPENSSL}/exchange"), size / 8),
            |b| {
                b.iter(|| {
                    let mut deriver = Deriver::new(&openssl_pkey).unwrap();
                    deriver.set_peer(black_box(&openssl_peer)).unwrap();
                    let z = deriver.derive_to_vec().unwrap();
                    let mut out = vec![0; p.len()];
                    let offset = out.len() - z.len();
                    out[offset..].copy_from_slice(&z);
                    black_box(out)
                })
            },
        );
        group.bench_function(
            BenchmarkId::new(format!("{VG}/parameters_from"), size / 8),
            |b| {
                b.iter(|| {
                    Parameters::from_components(black_box(&p), black_box(&g), q.as_deref()).unwrap()
                })
            },
        );
        group.bench_function(
            BenchmarkId::new(format!("{OPENSSL}/parameters_from"), size / 8),
            |b| {
                b.iter(|| {
                    Dh::from_pqg(
                        BigNum::from_slice(black_box(&p)).unwrap(),
                        q.as_ref().map(|q| BigNum::from_slice(q).unwrap()),
                        BigNum::from_slice(black_box(&g)).unwrap(),
                    )
                    .unwrap()
                })
            },
        );
        group.bench_function(BenchmarkId::new(format!("{VG}/generate"), size / 8), |b| {
            b.iter(|| black_box(&params).generate_private_key().unwrap())
        });
        group.bench_function(
            BenchmarkId::new(format!("{OPENSSL}/generate"), size / 8),
            |b| {
                b.iter(|| {
                    Dh::from_pqg(
                        BigNum::from_slice(&p).unwrap(),
                        q.as_ref().map(|q| BigNum::from_slice(q).unwrap()),
                        BigNum::from_slice(&g).unwrap(),
                    )
                    .unwrap()
                    .generate_key()
                    .unwrap()
                })
            },
        );
        group.bench_function(
            BenchmarkId::new(format!("{VG}/private_from"), size / 8),
            |b| {
                b.iter(|| {
                    PrivateKey::from_components(black_box(&params), black_box(&y), black_box(&x))
                        .unwrap()
                })
            },
        );
        group.bench_function(
            BenchmarkId::new(format!("{OPENSSL}/private_from"), size / 8),
            |b| {
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
            },
        );
        group.bench_function(
            BenchmarkId::new(format!("{VG}/public_from"), size / 8),
            |b| b.iter(|| PublicKey::from_components(black_box(&params), black_box(&y)).unwrap()),
        );
        group.bench_function(
            BenchmarkId::new(format!("{OPENSSL}/public_from"), size / 8),
            |b| {
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
            },
        );
        group.bench_function(
            BenchmarkId::new(format!("{VG}/components"), size / 8),
            |b| {
                b.iter(|| {
                    black_box(params.components());
                    black_box(key.public_key());
                    black_box(key.private_component());
                    black_box(key.public_key().component());
                    black_box(key.public_key().parameters());
                    black_box(params.key_size());
                })
            },
        );
        group.bench_function(
            BenchmarkId::new(format!("{OPENSSL}/components"), size / 8),
            |b| {
                b.iter(|| {
                    black_box(openssl_key.prime_p());
                    black_box(openssl_key.generator());
                    black_box(openssl_key.prime_q());
                    black_box(openssl_key.public_key());
                    black_box(openssl_key.private_key());
                    black_box(openssl_key.prime_p().num_bits());
                })
            },
        );
    }
    group.finish();
    let mut group = c.benchmark_group("ffdh_parameters");
    group.sample_size(10);
    for generator in [2, 5] {
        group.bench_function(BenchmarkId::new(format!("{VG}/g{generator}"), 64), |b| {
            b.iter(|| Parameters::generate(512, generator).unwrap())
        });
        group.bench_function(
            BenchmarkId::new(format!("{OPENSSL}/g{generator}"), 64),
            |b| b.iter(|| Dh::generate_params(512, generator).unwrap()),
        );
    }
    group.finish();
}
#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_c: &mut Criterion) {}
