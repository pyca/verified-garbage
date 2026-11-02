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
    use crate::{BenchDyn, OPENSSL, VG, fixed_tape};
    use criterion::BenchmarkId;
    use openssl::dsa::Dsa;
    use std::hint::black_box;
    use verified_garbage::dsa::Parameters;

    // verified-garbage searches from fixed tapes (`generate` but for
    // `getrandom`), so it tests the same candidates and witnesses in every
    // iteration. OpenSSL cannot be given its tapes, and draws from its own
    // generator.
    let mut group = c.benchmark_group("dsa_generate_parameters");
    group.sample_size(10);
    for bits in [1024, 2048, 3072] {
        // The legacy API used by rust-openssl chooses 160/256-bit q, unlike
        // the provider's default. Verify the comparison sizes before timing.
        let check = Dsa::generate_params(bits as u32).unwrap();
        assert_eq!(check.p().num_bits(), bits as i32);
        assert_eq!(check.q().num_bits(), if bits == 1024 { 160 } else { 256 });
        group.bench(BenchmarkId::new(VG, bits), |b| {
            b.iter(|| {
                let mut tape = fixed_tape(bits as u64);
                Parameters::generate_with_rng(black_box(bits), |buf| {
                    tape(buf);
                    Ok(())
                })
                .unwrap()
            })
        });
        group.bench(BenchmarkId::new(OPENSSL, bits), |b| {
            b.iter(|| Dsa::generate_params(black_box(bits as u32)).unwrap())
        });
    }
    group.finish();
}

#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}
