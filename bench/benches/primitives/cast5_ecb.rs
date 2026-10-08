//! CAST5 ECB, including key expansion and in-place encryption/decryption.
//!
//! aws-lc-rs has no CAST5, so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["cast5_ecb", "cast5"];

#[cfg(target_arch = "x86_64")]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::nid::Nid;
    use openssl::provider::Provider;
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::cast5_ecb::Cast5Ecb;

    use crate::{OPENSSL, SIZES, VG};

    // CAST5 is in OpenSSL 3's legacy provider; retain the default provider
    // for the other algorithms benchmarked by this process.
    let _legacy = Provider::try_load(None, "legacy", true).unwrap();
    let cipher = Cipher::from_nid(Nid::CAST5_ECB).unwrap();
    let key: Vec<_> = (0..16).map(|i| (17 * i + 3) as u8).collect();
    for (operation, encrypt, mode) in [
        ("encrypt", true, Mode::Encrypt),
        ("decrypt", false, Mode::Decrypt),
    ] {
        let mut group = c.benchmark_group(format!("cast5-ecb-{operation}"));
        for size in SIZES {
            group.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            let mut buffer = vec![0; size];
            group.bench_function(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    let ctx = Cast5Ecb::new(black_box(&key)).unwrap();
                    buffer.copy_from_slice(black_box(&data));
                    if encrypt {
                        ctx.encrypt(black_box(&mut buffer)).unwrap();
                    } else {
                        ctx.decrypt(black_box(&mut buffer)).unwrap();
                    }
                    black_box(&buffer);
                })
            });
            let mut output = vec![0; size + 8];
            group.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx = Crypter::new(cipher, mode, black_box(&key), None).unwrap();
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

#[cfg(not(target_arch = "x86_64"))]
pub fn bench(_: &mut Criterion) {}
