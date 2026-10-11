//! SM4-CFB128, including key expansion and in-place encryption/decryption,
//! beside OpenSSL.
//!
//! aws-lc-rs has no SM4, so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["sm4_cfb", "sm4"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::sm4_cfb::Sm4Cfb128;

    use crate::{OPENSSL, SIZES, VG};

    let key: [u8; 16] = core::array::from_fn(|i| (17 * i + 3) as u8);
    let iv = [0x3c; 16];
    for (operation, encrypt, mode) in [
        ("encrypt", true, Mode::Encrypt),
        ("decrypt", false, Mode::Decrypt),
    ] {
        let mut group = c.benchmark_group(format!("sm4-cfb128-{operation}"));
        for size in SIZES {
            group.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            let mut buffer = vec![0; size];
            group.bench_function(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    let ctx = Sm4Cfb128::new(black_box(&key));
                    let mut chain = black_box(iv);
                    buffer.copy_from_slice(black_box(&data));
                    if encrypt {
                        ctx.encrypt(&mut chain, black_box(&mut buffer));
                    } else {
                        ctx.decrypt(&mut chain, black_box(&mut buffer));
                    }
                    black_box(&buffer);
                })
            });
            let mut output = vec![0; size + 16];
            group.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx = Crypter::new(
                        Cipher::sm4_cfb128(),
                        mode,
                        black_box(&key),
                        Some(black_box(&iv)),
                    )
                    .unwrap();
                    let n = ctx.update(black_box(&data), &mut output).unwrap();
                    let n = n + ctx.finalize(&mut output[n..]).unwrap();
                    black_box(&output[..n]);
                })
            });
        }
        group.finish();
    }
}

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
