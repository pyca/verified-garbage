//! Blowfish-ECB, including key expansion, update, and unpadded
//! finalization.

use criterion::Criterion;

pub const USES: &[&str] = &["blowfish_ecb", "blowfish"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::provider::Provider;
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::blowfish_ecb::{BlowfishEcbDecryptor, BlowfishEcbEncryptor};

    use crate::{OPENSSL, SIZES, VG};

    // Blowfish is in OpenSSL 3's legacy provider; retain the default
    // provider for the other algorithms benchmarked by this process.
    let _legacy = Provider::try_load(None, "legacy", true).unwrap();
    let key = [0x42; 16];
    for (name, mode) in [
        ("blowfish-ecb-encrypt", Mode::Encrypt),
        ("blowfish-ecb-decrypt", Mode::Decrypt),
    ] {
        let mut g = c.benchmark_group(name);
        for size in SIZES {
            g.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            // Both libraries write into a buffer allocated once, outside the
            // timed code.
            let mut output = vec![0; size + 8];
            g.bench_function(BenchmarkId::new(VG, size), |b| match mode {
                Mode::Encrypt => b.iter(|| {
                    let mut ctx = BlowfishEcbEncryptor::new(black_box(&key)).unwrap();
                    let n = ctx.update(black_box(&data), &mut output).unwrap();
                    ctx.finalize().unwrap();
                    black_box(&output[..n]);
                }),
                Mode::Decrypt => b.iter(|| {
                    let mut ctx = BlowfishEcbDecryptor::new(black_box(&key)).unwrap();
                    let n = ctx.update(black_box(&data), &mut output).unwrap();
                    ctx.finalize().unwrap();
                    black_box(&output[..n]);
                }),
            });
            g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx =
                        Crypter::new(Cipher::bf_ecb(), mode, black_box(&key), None).unwrap();
                    ctx.pad(false);
                    let n = ctx.update(black_box(&data), &mut output).unwrap();
                    let n = n + ctx.finalize(&mut output[n..]).unwrap();
                    black_box(&output[..n]);
                })
            });
        }
        g.finish();
    }
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
