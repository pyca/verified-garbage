//! AES-CFB8, including key expansion and in-place encryption/decryption,
//! beside OpenSSL (aws-lc-rs has no CFB8).

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["aes_cfb8", "aes"];

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
    use verified_garbage::aes_cfb8::AesCfb8;

    use crate::{OPENSSL, SIZES, VG};

    let key: Vec<_> = (0..32).map(|i| (17 * i + 3) as u8).collect();
    let iv = [0x3c; 16];
    for (key_len, cipher) in [
        (16, Cipher::aes_128_cfb8()),
        (24, Cipher::aes_192_cfb8()),
        (32, Cipher::aes_256_cfb8()),
    ] {
        let key = &key[..key_len];
        for (operation, encrypt, mode) in [
            ("encrypt", true, Mode::Encrypt),
            ("decrypt", false, Mode::Decrypt),
        ] {
            let mut group = c.benchmark_group(format!("aes-cfb8-{operation}-{}", 8 * key_len));
            for size in SIZES {
                group.throughput(Throughput::Bytes(size as u64));
                let data = vec![0x5a; size];
                let mut buffer = vec![0; size];
                group.bench_function(BenchmarkId::new(VG, size), |b| {
                    b.iter(|| {
                        let ctx = AesCfb8::new(black_box(key)).unwrap();
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
                        let mut ctx =
                            Crypter::new(cipher, mode, black_box(key), Some(black_box(&iv)))
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
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
