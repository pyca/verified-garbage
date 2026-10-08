//! XTS-AES, including key expansion, the tweak's encryption and in-place
//! encryption of a data unit, beside OpenSSL (aws-lc-rs has no XTS, and
//! OpenSSL none with AES-192).

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["aes_xts", "aes"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::aes_xts::AesXts;

    use crate::{OPENSSL, SIZES, VG};

    let key: Vec<_> = (0..64).map(|i| (17 * i + 3) as u8).collect();
    let i = [0x3c; 16];
    for (key_len, cipher) in [
        (32, Some(Cipher::aes_128_xts())),
        (48, None),
        (64, Some(Cipher::aes_256_xts())),
    ] {
        let key = &key[..key_len];
        let mut group = c.benchmark_group(format!("aes-xts-{}", 4 * key_len));
        for size in SIZES {
            group.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            let mut buffer = vec![0; size];
            group.bench_function(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    let ctx = AesXts::new(black_box(key)).unwrap();
                    buffer.copy_from_slice(black_box(&data));
                    ctx.encrypt(black_box(&i), black_box(&mut buffer)).unwrap();
                    black_box(&buffer);
                })
            });
            let Some(cipher) = cipher else { continue };
            let mut output = vec![0; size + 16];
            group.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx =
                        Crypter::new(cipher, Mode::Encrypt, black_box(key), Some(black_box(&i)))
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

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
