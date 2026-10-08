//! Camellia ECB, including key expansion and in-place encryption/decryption.
//!
//! aws-lc-rs has no Camellia, so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["camellia_ecb", "camellia"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::camellia_ecb::CamelliaEcb;

    use crate::{OPENSSL, SIZES, VG};

    let key: Vec<_> = (0..32).map(|i| (17 * i + 3) as u8).collect();
    for (key_len, cipher) in [
        (16, Cipher::camellia_128_ecb()),
        (24, Cipher::camellia_192_ecb()),
        (32, Cipher::camellia_256_ecb()),
    ] {
        for (operation, encrypt, mode) in [
            ("encrypt", true, Mode::Encrypt),
            ("decrypt", false, Mode::Decrypt),
        ] {
            let mut group = c.benchmark_group(format!("camellia-ecb-{operation}-{key_len}"));
            for size in SIZES {
                group.throughput(Throughput::Bytes(size as u64));
                let data = vec![0x5a; size];
                let mut buffer = vec![0; size];
                group.bench_function(BenchmarkId::new(VG, size), |b| {
                    b.iter(|| {
                        let ctx = CamelliaEcb::new(black_box(&key[..key_len])).unwrap();
                        buffer.copy_from_slice(black_box(&data));
                        if encrypt {
                            ctx.encrypt(black_box(&mut buffer)).unwrap();
                        } else {
                            ctx.decrypt(black_box(&mut buffer)).unwrap();
                        }
                        black_box(&buffer);
                    })
                });
                let mut output = vec![0; size + 16];
                group.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                    b.iter(|| {
                        let mut ctx =
                            Crypter::new(cipher, mode, black_box(&key[..key_len]), None).unwrap();
                        ctx.pad(false);
                        let n = ctx.update(black_box(&data), &mut output).unwrap();
                        let n = n + ctx.finalize(&mut output[n..]).unwrap();
                        black_box(&output[..n]);
                    })
                });
            }
            group.finish();
        }
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
