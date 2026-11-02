//! Blowfish-CFB64, including key expansion and in-place encryption/decryption.
//!
//! aws-lc-rs has no Blowfish, so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["blowfish_cfb", "blowfish"];

#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::provider::Provider;
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::blowfish_cfb::BlowfishCfb64;

    use crate::{BenchDyn, OPENSSL, SIZES, VG};

    // Blowfish is in OpenSSL 3's legacy provider; retain the default
    // provider for the other algorithms benchmarked by this process.
    let _legacy = Provider::try_load(None, "legacy", true).unwrap();
    let key = [0x42; 16];
    let iv = [0x3c; 8];
    for (operation, encrypt, mode) in [
        ("encrypt", true, Mode::Encrypt),
        ("decrypt", false, Mode::Decrypt),
    ] {
        let mut group = c.benchmark_group(format!("blowfish-cfb-{operation}"));
        for size in SIZES {
            group.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            let mut buffer = crate::InPlace::new(size, &data);
            group.bench(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    let ctx = BlowfishCfb64::new(black_box(&key)).unwrap();
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
            let mut output = vec![0; size + 8];
            group.bench(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx = Crypter::new(
                        Cipher::bf_cfb64(),
                        mode,
                        black_box(&key),
                        Some(black_box(&iv)),
                    )
                    .unwrap();
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

#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
