//! SM4-CTR, including key expansion and in-place encryption.
//!
//! aws-lc-rs has no SM4, so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["sm4_ctr", "sm4"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::sm4_ctr::Sm4Ctr;

    use crate::{OPENSSL, SIZES, VG};

    let cipher = Cipher::sm4_ctr();
    let key: [u8; 16] = core::array::from_fn(|i| (17 * i + 3) as u8);
    let iv: [u8; 16] = core::array::from_fn(|i| (5 * i + 1) as u8);
    let mut group = c.benchmark_group("sm4-ctr");
    for size in SIZES {
        group.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mut buffer = vec![0; size];
        group.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let ctx = Sm4Ctr::new(black_box(&key));
                let mut ctr = black_box(iv);
                buffer.copy_from_slice(black_box(&data));
                ctx.apply_keystream(&mut ctr, black_box(&mut buffer));
                black_box(&buffer);
            })
        });
        let mut output = vec![0; size + 16];
        group.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut ctx =
                    Crypter::new(cipher, Mode::Encrypt, black_box(&key), Some(black_box(&iv)))
                        .unwrap();
                let n = ctx.update(black_box(&data), &mut output).unwrap();
                let n = n + ctx.finalize(&mut output[n..]).unwrap();
                black_box(&output[..n]);
            })
        });
    }
    group.finish();
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
