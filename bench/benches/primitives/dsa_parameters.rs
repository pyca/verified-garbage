//! Complete DSA parameter generation beside OpenSSL.
use criterion::Criterion;

pub const USES: &[&str] = &["dsa", "rsa_mont", "miller_rabin", "sha1", "sha256"];

#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    use crate::{OPENSSL, VG};
    use criterion::BenchmarkId;
    use openssl::dsa::Dsa;
    use std::hint::black_box;
    use verified_garbage::dsa::Parameters;

    let mut group = c.benchmark_group("dsa_generate_parameters");
    group.sample_size(10);
    for bits in [1024, 2048, 3072] {
        // The legacy API used by rust-openssl chooses 160/256-bit q, unlike
        // the provider's default. Verify the comparison sizes before timing.
        let check = Dsa::generate_params(bits as u32).unwrap();
        assert_eq!(check.p().num_bits(), bits as i32);
        assert_eq!(check.q().num_bits(), if bits == 1024 { 160 } else { 256 });
        group.bench_function(BenchmarkId::new(VG, bits), |b| {
            b.iter(|| Parameters::generate(black_box(bits)).unwrap())
        });
        group.bench_function(BenchmarkId::new(OPENSSL, bits), |b| {
            b.iter(|| Dsa::generate_params(black_box(bits as u32)).unwrap())
        });
    }
    group.finish();

    // The same search from fixed tapes: every iteration, and the base and
    // head of a comparison, test the same candidates and witnesses, so the
    // timing compares implementations rather than how many candidates the
    // random tapes happened to need. OpenSSL cannot be given its tapes.
    let mut group = c.benchmark_group("dsa_generate_parameters_fixed");
    group.sample_size(10);
    for bits in [1024, 2048, 3072] {
        group.bench_function(BenchmarkId::new(VG, bits), |b| {
            b.iter(|| {
                let mut tape = FixedTape(0x9E37_79B9_7F4A_7C15 ^ bits as u64);
                Parameters::generate_with_rng(black_box(bits), |buf| {
                    tape.fill(buf);
                    Ok(())
                })
                .unwrap()
            })
        });
    }
    group.finish();
}

/// A deterministic byte stream (xorshift64), the tapes of the fixed-tape
/// benchmark.
#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
struct FixedTape(u64);

#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
impl FixedTape {
    fn fill(&mut self, buf: &mut [u8]) {
        for b in buf {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            *b = self.0 as u8;
        }
    }
}

#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}
