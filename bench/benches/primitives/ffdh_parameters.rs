//! Safe-prime parameter generation on repeatable random tapes.
use criterion::Criterion;

pub const USES: &[&str] = &["ffdh", "rsa_mont", "miller_rabin"];

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
    use openssl::dh::Dh;
    use std::{cell::OnceCell, hint::black_box};
    use verified_garbage::ffdh::{Error, Parameters};

    let mut group = c.benchmark_group("ffdh_generate_parameters");
    group.sample_size(10);
    for bits in [512, 1024] {
        let random = OnceCell::new();
        group.bench(BenchmarkId::new(VG, bits), |b| {
            // Search the same candidates and witnesses on both revisions.
            // Use the first stream in a fixed sequence that completes within
            // the API's candidate limit; selection does not use elapsed time.
            let tape = random.get_or_init(|| {
                for seed in bits as u64.. {
                    let mut fill = fixed_tape(seed);
                    let mut tape = Vec::new();
                    match Parameters::generate_with_rng(bits, 2, |out| {
                        fill(out);
                        tape.extend_from_slice(out);
                        Ok::<_, ()>(())
                    }) {
                        Ok(_) => return tape,
                        Err(Error::TooManyIterations) => {}
                        Err(error) => panic!("parameter generation failed: {error:?}"),
                    }
                }
                unreachable!()
            });
            b.iter(|| {
                let mut remaining = tape.as_slice();
                Parameters::generate_with_rng(black_box(bits), 2, |out| {
                    let (draw, rest) = remaining.split_at(out.len());
                    out.copy_from_slice(draw);
                    remaining = rest;
                    Ok::<_, ()>(())
                })
                .unwrap()
            })
        });
        // OpenSSL draws from its own generator, as in the RSA and DSA
        // parameter-generation benchmarks; its search is a different draw.
        group.bench(BenchmarkId::new(OPENSSL, bits), |b| {
            b.iter(|| Dh::generate_params(black_box(bits as u32), 2).unwrap())
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
