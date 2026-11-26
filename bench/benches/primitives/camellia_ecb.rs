//! Camellia ECB, including key expansion and in-place encryption/decryption.
//!
//! aws-lc-rs has no Camellia, so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["camellia_ecb", "camellia"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::cipher::camellia::CamelliaEcb;

    use crate::{BenchDyn, OPENSSL, VG};

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
            for size in [16, 64, 128, 144, 1024, 16384] {
                group.throughput(Throughput::Bytes(size as u64));
                let data = vec![0x5a; size];
                let mut buffer = crate::InPlace::new(size, &data);
                group.bench(BenchmarkId::new(VG, size), |b| {
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
                group.bench(BenchmarkId::new(OPENSSL, size), |b| {
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
            let mut reused =
                c.benchmark_group(format!("camellia-ecb-{operation}-reused-{key_len}"));
            for size in [16, 64, 128, 144, 1024, 16384] {
                reused.throughput(Throughput::Bytes(size as u64));
                let data = vec![0x5a; size];
                let mut buffer = crate::InPlace::new(size, &data);
                let ctx = CamelliaEcb::new(&key[..key_len]).unwrap();
                let mut reference = Crypter::new(cipher, mode, &key[..key_len], None).unwrap();
                reference.pad(false);
                let mut expected = vec![0; size + 16];
                // Check two consecutive chunks, including the mode's chaining state.
                for _ in 0..2 {
                    let mut checked = data.clone();
                    if encrypt {
                        ctx.encrypt(&mut checked).unwrap();
                    } else {
                        ctx.decrypt(&mut checked).unwrap();
                    }
                    let n = reference.update(&data, &mut expected).unwrap();
                    assert_eq!(checked, expected[..n]);
                }
                reused.bench(BenchmarkId::new(VG, size), |b| {
                    b.iter(|| {
                        buffer.copy_from_slice(black_box(&data));
                        if encrypt {
                            ctx.encrypt(black_box(&mut buffer)).unwrap();
                        } else {
                            ctx.decrypt(black_box(&mut buffer)).unwrap();
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
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
