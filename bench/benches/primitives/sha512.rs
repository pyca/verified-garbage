//! SHA-512.

use criterion::Criterion;

pub const USES: &[&str] = &["sha512"];

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}

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
    use verified_garbage::hashes::sha512::Sha512;

    use crate::hash_group;

    hash_group(
        c,
        "sha512",
        Sha512::digest,
        MessageDigest::sha512(),
        Some(&aws_lc_rs::digest::SHA512),
    );

    // Measurement only: the same digest with the stack pointer moved down
    // by `N` bytes.
    #[inline(never)]
    fn padded<const N: usize>(data: &[u8]) {
        let mut p = [0u8; N];
        std::hint::black_box(&mut p);
        std::hint::black_box(Sha512::digest(std::hint::black_box(data)));
        std::hint::black_box(&p);
    }
    let data = vec![0x5au8; 16384];
    let mut g = c.benchmark_group("sha512pad");
    macro_rules! pads {
        ($($n:literal)*) => {$(
            g.bench_function(criterion::BenchmarkId::new("verified-garbage", $n), |b| {
                b.iter(|| padded::<$n>(&data))
            });
        )*};
    }
    pads!(0 256 512 768 1024 1280 1536 1792 2048 2304 2560 2816 3072 3328 3584 3840);
    g.finish();
}
