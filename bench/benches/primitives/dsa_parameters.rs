//! Complete DSA parameter generation beside OpenSSL.
use criterion::Criterion;

pub const USES: &[&str] = &["dsa", "rsa_mont", "miller_rabin", "sha1", "sha256"];

#[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
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
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
pub fn bench(_: &mut Criterion) {}
