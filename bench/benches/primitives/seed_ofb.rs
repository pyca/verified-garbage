//! SEED-OFB, including key expansion and in-place encryption.
//!
//! aws-lc-rs has no SEED, so there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["seed_ofb", "seed"];

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
    use verified_garbage::cipher::seed::SeedOfb;

    use crate::{BenchDyn, OPENSSL, VG};

    // SEED is in OpenSSL 3's legacy provider; retain the default provider
    // for the other algorithms benchmarked by this process.
    let _legacy = Provider::try_load(None, "legacy", true).unwrap();
    let cipher = Cipher::from_nid(Nid::SEED_OFB128).unwrap();
    let key: [u8; 16] = core::array::from_fn(|i| (17 * i + 3) as u8);
    let iv = [0x3c; 16];
    let mut group = c.benchmark_group("seed-ofb");
    for size in [15, 16, 17, 96, 112, 113, 256, 257, 1024, 16384] {
        group.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mut buffer = crate::InPlace::new(size, &data);
        {
            let ctx = SeedOfb::new(&key, &iv);
            let mut checked = data.clone();
            ctx.apply_keystream_final(&mut checked);
            let mut reference = Crypter::new(cipher, Mode::Encrypt, &key, Some(&iv)).unwrap();
            reference.pad(false);
            let mut expected = vec![0; size + 16];
            let n = reference.update(&data, &mut expected).unwrap();
            let n = n + reference.finalize(&mut expected[n..]).unwrap();
            assert_eq!(checked, expected[..n]);
        }
        group.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let ctx = SeedOfb::new(black_box(&key), &black_box(iv));
                buffer.copy_from_slice(black_box(&data));
                ctx.apply_keystream_final(black_box(&mut buffer));
                black_box(&buffer);
            })
        });
        let mut output = vec![0; size + 16];
        group.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut ctx =
                    Crypter::new(cipher, Mode::Encrypt, black_box(&key), Some(black_box(&iv)))
                        .unwrap();
                let n = ctx.update(black_box(&data), &mut output).unwrap();
                let n = n + ctx.finalize(&mut output[n..]).unwrap();
                black_box(&output[..n]);
            })
        });
    }
    group.finish();
    let mut reused = c.benchmark_group("seed-ofb-reused");
    for size in [16, 64, 96, 112, 128, 256, 1024, 16384] {
        reused.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mut buffer = crate::InPlace::new(size, &data);
        let mut ctx = SeedOfb::new(&key, &iv);
        let mut reference = Crypter::new(cipher, Mode::Encrypt, &key, Some(&iv)).unwrap();
        reference.pad(false);
        let mut expected = vec![0; size + 16];
        // Check consecutive chunks, including each mode's chaining state.
        for _ in 0..2 {
            let mut checked = data.clone();
            ctx.apply_keystream(&mut checked).unwrap();
            let n = reference.update(&data, &mut expected).unwrap();
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

#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
