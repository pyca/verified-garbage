//! SHA-3 and SHAKE.

use criterion::Criterion;

pub const USES: &[&str] = &["sha3"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha3::{
        Sha3_224, Sha3_256, Sha3_384, Sha3_512, Shake128, Shake256,
    };

    use crate::hash_group_sizes;
    const SIZES: &[usize] = &[
        0, 1, 7, 8, 15, 16, 31, 32, 63, 64, 65, 71, 72, 73, 103, 104, 105, 135, 136, 137, 143, 144,
        145, 1024, 16384,
    ];
    hash_group_sizes(
        c,
        "sha3-224",
        SIZES,
        Sha3_224::digest,
        MessageDigest::sha3_224(),
        None,
    );
    hash_group_sizes(
        c,
        "sha3-256",
        SIZES,
        Sha3_256::digest,
        MessageDigest::sha3_256(),
        Some(&aws_lc_rs::digest::SHA3_256),
    );
    hash_group_sizes(
        c,
        "sha3-384",
        SIZES,
        Sha3_384::digest,
        MessageDigest::sha3_384(),
        Some(&aws_lc_rs::digest::SHA3_384),
    );
    hash_group_sizes(
        c,
        "sha3-512",
        SIZES,
        Sha3_512::digest,
        MessageDigest::sha3_512(),
        Some(&aws_lc_rs::digest::SHA3_512),
    );
    xof_group(c, "shake128", Shake128::digest, MessageDigest::shake_128());
    xof_group(c, "shake256", Shake256::digest, MessageDigest::shake_256());
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

/// Benchmarks the extendable-output function `vg` against OpenSSL's `md`,
/// with 32 bytes of output.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn xof_group(
    c: &mut Criterion,
    name: &str,
    vg: fn(&[u8], &mut [u8]),
    md: openssl::hash::MessageDigest,
) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::hash::Hasher;

    use crate::{BenchDyn, OPENSSL, SIZES, VG};
    let mut g = c.benchmark_group(name);
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let mut out = [0u8; 32];
        g.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| vg(black_box(&data), &mut out))
        });
        g.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut h = Hasher::new(md).unwrap();
                h.update(black_box(&data)).unwrap();
                h.finish_xof(&mut out).unwrap();
            })
        });
    }
    g.finish();
}
