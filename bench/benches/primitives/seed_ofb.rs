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
    use verified_garbage::seed_ofb::SeedOfb;

    use crate::{BenchDyn, OPENSSL, SIZES, VG};

    // SEED is in OpenSSL 3's legacy provider; retain the default provider
    // for the other algorithms benchmarked by this process.
    let _legacy = Provider::try_load(None, "legacy", true).unwrap();
    let cipher = Cipher::from_nid(Nid::SEED_OFB128).unwrap();
    let key: Vec<_> = (0..16).map(|i| (17 * i + 3) as u8).collect();
    let iv = [0x3c; 16];
    let mut group = c.benchmark_group("seed-ofb");
    for size in SIZES {
        group.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mut buffer = crate::InPlace::new(size, &data);
        group.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let ctx = SeedOfb::new(black_box(&key)).unwrap();
                let mut chain = black_box(iv);
                buffer.copy_from_slice(black_box(&data));
                ctx.apply_keystream(&mut chain, black_box(&mut buffer));
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
