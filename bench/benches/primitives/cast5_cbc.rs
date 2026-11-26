//! CAST5-CBC, including key expansion and in-place encryption/decryption.
//!
//! aws-lc-rs has no CAST5, so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["cast5_cbc", "cast5"];

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
    use openssl::nid::Nid;
    use openssl::provider::Provider;
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::cipher::cast5::{Cast5CbcDecryptor, Cast5CbcEncryptor};

    use crate::{BenchDyn, OPENSSL, VG};

    // CAST5 is in OpenSSL 3's legacy provider; retain the default provider
    // for the other algorithms benchmarked by this process.
    let _legacy = Provider::try_load(None, "legacy", true).unwrap();
    let cipher = Cipher::from_nid(Nid::CAST5_CBC).unwrap();
    let full_key: [u8; 16] = core::array::from_fn(|i| (17 * i + 3) as u8);
    let iv = [0x3c; 8];
    for key_len in [5, 16] {
        let key = &full_key[..key_len];
        let suffix = if key_len == 16 {
            String::new()
        } else {
            format!("-{key_len}")
        };
        for (operation, encrypt, mode) in [
            ("encrypt", true, Mode::Encrypt),
            ("decrypt", false, Mode::Decrypt),
        ] {
            let mut group = c.benchmark_group(format!("cast5-cbc-{operation}{suffix}"));
            for size in [8, 64, 120, 128, 136, 1024, 16384] {
                group.throughput(Throughput::Bytes(size as u64));
                let data = vec![0x5a; size];
                let mut buffer = crate::InPlace::new(size, &data);
                group.bench(BenchmarkId::new(VG, size), |b| {
                    b.iter(|| {
                        buffer.copy_from_slice(black_box(&data));
                        if encrypt {
                            let mut ctx =
                                Cast5CbcEncryptor::new(black_box(key), &black_box(iv)).unwrap();
                            ctx.encrypt(black_box(&mut buffer)).unwrap();
                        } else {
                            let mut ctx =
                                Cast5CbcDecryptor::new(black_box(key), &black_box(iv)).unwrap();
                            ctx.decrypt(black_box(&mut buffer)).unwrap();
                        }
                        black_box(&buffer);
                    })
                });
                let mut output = vec![0; size + 16];
                group.bench(BenchmarkId::new(OPENSSL, size), |b| {
                    b.iter(|| {
                        let mut ctx =
                            Crypter::new(cipher, mode, black_box(key), Some(black_box(&iv)))
                                .unwrap();
                        ctx.pad(false);
                        let n = ctx.update(black_box(&data), &mut output).unwrap();
                        let n = n + ctx.finalize(&mut output[n..]).unwrap();
                        black_box(&output[..n]);
                    })
                });
            }
            group.finish();
            let mut reused = c.benchmark_group(format!("cast5-cbc-{operation}-reused{suffix}"));
            for size in [8, 64, 120, 128, 136, 1024, 16384] {
                reused.throughput(Throughput::Bytes(size as u64));
                let data = vec![0x5a; size];
                let mut buffer = crate::InPlace::new(size, &data);
                let mut enc = Cast5CbcEncryptor::new(key, &iv).unwrap();
                let mut dec = Cast5CbcDecryptor::new(key, &iv).unwrap();
                let mut reference = Crypter::new(cipher, mode, key, Some(&iv)).unwrap();
                reference.pad(false);
                let mut expected = vec![0; size + 16];
                // Check consecutive chunks, including each mode's chaining state.
                for _ in 0..2 {
                    let mut checked = data.clone();
                    if encrypt {
                        enc.encrypt(&mut checked).unwrap();
                    } else {
                        dec.decrypt(&mut checked).unwrap();
                    }
                    let n = reference.update(&data, &mut expected).unwrap();
                    assert_eq!(checked, expected[..n]);
                }
                reused.bench(BenchmarkId::new(VG, size), |b| {
                    b.iter(|| {
                        buffer.copy_from_slice(black_box(&data));
                        if encrypt {
                            enc.encrypt(black_box(&mut buffer)).unwrap();
                        } else {
                            dec.decrypt(black_box(&mut buffer)).unwrap();
                        }
                        black_box(&buffer);
                    })
                });
            }
            reused.finish();
        }
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
