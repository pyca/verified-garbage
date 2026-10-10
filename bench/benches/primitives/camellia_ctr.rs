//! Camellia-CTR, including key expansion and in-place encryption.
//!
//! aws-lc-rs has no Camellia, so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["camellia_ctr", "camellia"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher::Cipher;
    use openssl::cipher_ctx::CipherCtx;
    use verified_garbage::camellia_ctr::CamelliaCtr;

    use crate::{OPENSSL, SIZES, VG};

    let key: Vec<_> = (0..32).map(|i| (17 * i + 3) as u8).collect();
    let iv: [u8; 16] = core::array::from_fn(|i| (5 * i + 1) as u8);
    for key_len in [16, 24, 32] {
        let key = &key[..key_len];
        let cipher = Cipher::fetch(None, &format!("CAMELLIA-{}-CTR", 8 * key_len), None).unwrap();
        let mut group = c.benchmark_group(format!("camellia-ctr-{key_len}"));
        for size in SIZES {
            group.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            let mut buffer = vec![0; size];
            group.bench_function(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    let ctx = CamelliaCtr::new(black_box(key)).unwrap();
                    let mut ctr = black_box(iv);
                    buffer.copy_from_slice(black_box(&data));
                    ctx.apply_keystream(&mut ctr, black_box(&mut buffer));
                    black_box(&buffer);
                })
            });
            let mut output = vec![0; size + 16];
            group.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx = CipherCtx::new().unwrap();
                    ctx.encrypt_init(Some(&cipher), Some(black_box(key)), Some(black_box(&iv)))
                        .unwrap();
                    let n = ctx
                        .cipher_update(black_box(&data), Some(&mut output))
                        .unwrap();
                    let n = n + ctx.cipher_final(&mut output[n..]).unwrap();
                    black_box(&output[..n]);
                })
            });
        }
        group.finish();
    }
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
