//! Camellia-CTR, including key expansion and in-place encryption.
//!
//! aws-lc-rs has no Camellia, so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["camellia_ctr", "camellia"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher::Cipher;
    use openssl::cipher_ctx::CipherCtx;
    use verified_garbage::cipher::camellia::CamelliaCtr;

    use crate::{BenchDyn, OPENSSL, VG};

    let key: Vec<_> = (0..32).map(|i| (17 * i + 3) as u8).collect();
    let iv: [u8; 16] = core::array::from_fn(|i| (5 * i + 1) as u8);
    for key_len in [16, 24, 32] {
        let key = &key[..key_len];
        let cipher = Cipher::fetch(None, &format!("CAMELLIA-{}-CTR", 8 * key_len), None).unwrap();
        let mut group = c.benchmark_group(format!("camellia-ctr-{key_len}"));
        for size in [16, 64, 128, 144, 1024, 16384] {
            group.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            let mut buffer = crate::InPlace::new(size, &data);
            group.bench(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    let ctx = CamelliaCtr::new(black_box(key), &black_box(iv)).unwrap();
                    buffer.copy_from_slice(black_box(&data));
                    ctx.apply_keystream_final(black_box(&mut buffer));
                    black_box(&buffer);
                })
            });
            let mut output = vec![0; size + 16];
            group.bench(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx = CipherCtx::new().unwrap();
                    ctx.encrypt_init(Some(&cipher), Some(black_box(key)), Some(black_box(&iv)))
                        .unwrap();
                    let n = ctx
                        .cipher_update(black_box(&data), Some(&mut output))
                        .unwrap();
                    let n = n + ctx.cipher_final(&mut output[n..]).unwrap();
                    black_box(&output[..n]);
                })
            });
        }
        group.finish();
        let mut reused = c.benchmark_group(format!("camellia-ctr-reused-{}", 8 * key_len));
        for size in [16, 64, 128, 144, 1024, 16384] {
            reused.throughput(Throughput::Bytes(size as u64));
            let data = vec![0x5a; size];
            let mut buffer = crate::InPlace::new(size, &data);
            let mut ctx = CamelliaCtr::new(key, &iv).unwrap();
            let mut reference = CipherCtx::new().unwrap();
            reference
                .encrypt_init(Some(&cipher), Some(key), Some(&iv))
                .unwrap();
            let mut expected = vec![0; size + 16];
            // Check two consecutive chunks, including the mode's chaining state.
            for _ in 0..2 {
                let mut checked = data.clone();
                ctx.apply_keystream(&mut checked).unwrap();
                let n = reference.cipher_update(&data, Some(&mut expected)).unwrap();
                assert_eq!(checked, expected[..n]);
            }
            reused.bench(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    buffer.copy_from_slice(black_box(&data));
                    ctx.apply_keystream(black_box(&mut buffer)).unwrap();
                    black_box(&buffer);
                })
            });
        }
        reused.finish();
    }
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
