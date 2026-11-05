//! The generation of an RSA key.

use criterion::Criterion;

pub const USES: &[&str] = &["rsa_keygen", "miller_rabin"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use std::cell::OnceCell;
    use std::hint::black_box;

    use aws_lc_rs::rsa::{KeyPair, KeySize};
    use criterion::BenchmarkId;
    use openssl::rsa::Rsa;
    use verified_garbage::rsa::keygen::generate_from;

    use crate::{AWS_LC, BenchDyn, OPENSSL, VG};
    // Keys of 2048, 3072 and 4096 bits with `e = 65537` (only 2048 on ARM,
    // to keep the larger generations off its job); the ids' size is the
    // modulus' bytes. The number of candidates varies from one prime to the
    // next, so verified-garbage's key is from fixed octets (`generate(bits,
    // e)` but for `getrandom`), and a slowdown is the code's, not the draw's:
    // two primes, the key from them, its check, and the pairwise consistency
    // test. So that the draw is a typical one, they are the stream, of the
    // streams of nine fixed seeds (splitmix64), whose key reads the median
    // number of octets. OpenSSL's `RSA_generate_key_ex` draws from its own
    // generator, and so does aws-lc-rs's `KeyPair::generate` (AWS-LC's, which
    // also checks the key with `RSA_check_key`).
    let mut g = c.benchmark_group("rsa_keygen_generate");
    g.sample_size(10);
    let sizes = [
        (2048, KeySize::Rsa2048),
        (3072, KeySize::Rsa3072),
        (4096, KeySize::Rsa4096),
    ];
    for &(bits, size) in &sizes[..if cfg!(target_arch = "arm") { 1 } else { 3 }] {
        let rand = OnceCell::new();
        g.bench(BenchmarkId::new(VG, bits / 8), |b| {
            let rand = rand.get_or_init(|| {
                let mut draws: Vec<(usize, Vec<u8>)> = (0..9)
                    .map(|i| {
                        let rand =
                            fixed_octets(bits + i, |r| generate_from(bits, &[1, 0, 1], r).is_ok());
                        (generate_from(bits, &[1, 0, 1], &rand).unwrap().1, rand)
                    })
                    .collect();
                draws.sort_by_key(|d| d.0);
                draws.swap_remove(4).1
            });
            b.iter(|| {
                generate_from(black_box(bits), black_box(&[1, 0, 1]), black_box(rand)).unwrap()
            })
        });
        g.bench(BenchmarkId::new(OPENSSL, bits / 8), |b| {
            b.iter(|| Rsa::generate(black_box(bits as u32)).unwrap())
        });
        g.bench(BenchmarkId::new(AWS_LC, bits / 8), |b| {
            b.iter(|| KeyPair::generate(black_box(size)).unwrap())
        });
    }
    g.finish();
}

/// The shortest stream of octets from a splitmix64 generator seeded with
/// `seed`, grown by doubling from `seed / 4` octets, that is `enough`.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
fn fixed_octets(seed: usize, enough: impl Fn(&[u8]) -> bool) -> Vec<u8> {
    let start = seed / 4;
    let mut seed = seed as u64;
    let mut next = || {
        seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let z = (seed ^ (seed >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        let z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    let mut rand: Vec<u8> = Vec::new();
    while !enough(&rand) {
        for _ in 0..(rand.len() / 8).max(start / 8) {
            rand.extend(next().to_le_bytes());
        }
    }
    rand
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
