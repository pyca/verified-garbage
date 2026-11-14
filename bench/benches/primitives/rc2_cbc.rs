//! RC2-CBC, including initialization and in-place encryption/decryption.

use criterion::Criterion;

pub const USES: &[&str] = &["rc2_cbc", "rc2"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::provider::Provider;
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::cipher::rc2::{Rc2CbcDecryptor, Rc2CbcEncryptor};

    use crate::{BenchDyn, OPENSSL, SIZES, VG};

    // RC2 is in OpenSSL 3's legacy provider; retain the default provider
    // for the other algorithms benchmarked by this process.
    let _legacy = Provider::try_load(None, "legacy", true).unwrap();
    let key = [0x42; 16];
    let iv = [0x24; 8];
    for (name, mode) in [
        ("rc2-cbc-encrypt", Mode::Encrypt),
        ("rc2-cbc-decrypt", Mode::Decrypt),
    ] {
        let mut g = c.benchmark_group(name);
        for size in SIZES {
            g.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            // Allocate the OpenSSL output and the in-place buffer outside the
            // timed code.
            let mut output = vec![0; size + 8];
            let mut buffer = crate::InPlace::new(size, &data);
            g.bench(BenchmarkId::new(VG, size), |b| match mode {
                Mode::Encrypt => b.iter(|| {
                    let mut ctx = Rc2CbcEncryptor::new(black_box(&key), black_box(&iv)).unwrap();
                    buffer.copy_from_slice(black_box(&data));
                    ctx.encrypt(black_box(&mut buffer)).unwrap();
                    black_box(&buffer);
                }),
                Mode::Decrypt => b.iter(|| {
                    let mut ctx = Rc2CbcDecryptor::new_with_effective_bits(
                        black_box(&key),
                        black_box(&iv),
                        128,
                    )
                    .unwrap();
                    buffer.copy_from_slice(black_box(&data));
                    ctx.decrypt(black_box(&mut buffer)).unwrap();
                    black_box(&buffer);
                }),
            });
            g.bench(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx = Crypter::new(
                        Cipher::rc2_cbc(),
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
        g.finish();
    }
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}
