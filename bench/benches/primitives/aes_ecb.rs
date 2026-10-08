//! AES-ECB, including key expansion and in-place encryption/decryption.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["aes_ecb", "aes"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::cipher::{
        AES_128, AES_192, AES_256, DecryptingKey, DecryptionContext, EncryptingKey,
        UnboundCipherKey,
    };
    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::aes_ecb::AesEcb;

    use crate::{AWS_LC, OPENSSL, SIZES, VG};

    let key: Vec<_> = (0..32).map(|i| (17 * i + 3) as u8).collect();
    for (key_len, cipher, algorithm) in [
        (16, Cipher::aes_128_ecb(), &AES_128),
        (24, Cipher::aes_192_ecb(), &AES_192),
        (32, Cipher::aes_256_ecb(), &AES_256),
    ] {
        let key = &key[..key_len];
        for (operation, encrypt, mode) in [
            ("encrypt", true, Mode::Encrypt),
            ("decrypt", false, Mode::Decrypt),
        ] {
            let mut group = c.benchmark_group(format!("aes-ecb-{operation}-{}", 8 * key_len));
            for size in SIZES {
                group.throughput(Throughput::Bytes(size as u64));
                let data = vec![0x5a; size];
                let mut buffer = vec![0; size];
                group.bench_function(BenchmarkId::new(VG, size), |b| {
                    b.iter(|| {
                        let ctx = AesEcb::new(black_box(key)).unwrap();
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
                        let mut ctx = Crypter::new(cipher, mode, black_box(key), None).unwrap();
                        ctx.pad(false);
                        let n = ctx.update(black_box(&data), &mut output).unwrap();
                        let n = n + ctx.finalize(&mut output[n..]).unwrap();
                        black_box(&output[..n]);
                    })
                });
                group.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
                    b.iter(|| {
                        let unbound = UnboundCipherKey::new(algorithm, black_box(key)).unwrap();
                        buffer.copy_from_slice(black_box(&data));
                        if encrypt {
                            let ctx = EncryptingKey::ecb(unbound).unwrap();
                            ctx.encrypt(black_box(&mut buffer)).unwrap();
                        } else {
                            let ctx = DecryptingKey::ecb(unbound).unwrap();
                            ctx.decrypt(black_box(&mut buffer), DecryptionContext::None)
                                .unwrap();
                        }
                        black_box(&buffer);
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
