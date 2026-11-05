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
    use verified_garbage::rsa::keygen::generate_with_rng;

    use crate::{AWS_LC, BenchDyn, OPENSSL, VG};
    // Keys of 2048, 3072 and 4096 bits with `e = 65537` (only 2048 on ARM,
    // to keep the larger generations off its job); the ids' size is the
    // modulus' bytes. The number of candidates varies from one prime to the
    // next, so verified-garbage's key is from a fixed tape (`generate(bits,
    // e)` but for `getrandom`), and a slowdown is the code's, not the draw's:
    // two primes, and the key from them and its check. So that the draw is a
    // typical one, the tape is the octets drawn from the stream, of the
    // streams of nine fixed seeds (splitmix64), whose key draws the median
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
                let mut tapes: Vec<Vec<u8>> = (0..9)
                    .map(|i| {
                        let mut next = splitmix64(bits + i);
                        let mut tape = Vec::new();
                        generate_with_rng(bits, &[1, 0, 1], |buf| {
                            buf.fill_with(&mut next);
                            tape.extend_from_slice(buf);
                            Ok(())
                        })
                        .unwrap();
                        tape
                    })
                    .collect();
                tapes.sort_by_key(Vec::len);
                tapes.swap_remove(4)
            });
            b.iter(|| {
                // The generation draws the same octets, in the same pieces,
                // as it did from the stream.
                let mut rest = &rand[..];
                generate_with_rng(black_box(bits), black_box(&[1, 0, 1]), |buf| {
                    let (now, later) = rest.split_at(buf.len());
                    buf.copy_from_slice(now);
                    rest = later;
                    Ok(())
                })
                .unwrap()
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

/// The octets of a splitmix64 generator seeded with `seed`.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
fn splitmix64(seed: usize) -> impl FnMut() -> u8 {
    let mut seed = seed as u64;
    let mut octets = [0u8; 8];
    let mut used = octets.len();
    move || {
        if used == octets.len() {
            seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let z = (seed ^ (seed >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            let z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            octets = (z ^ (z >> 31)).to_le_bytes();
            used = 0;
        }
        used += 1;
        octets[used - 1]
    }
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
