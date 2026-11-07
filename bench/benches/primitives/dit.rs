//! `dit::scope`: many short calls under one turn of data independent
//! timing. HMAC-SHA-256 fed 64 bytes per `update`, as outside a scope
//! (`hmac-sha256-updates`, next to OpenSSL's `Signer::update` in the same
//! pieces) and inside one (`hmac-sha256-updates-dit-scope`, which OpenSSL
//! has no equivalent of). On a CPU without data independent timing, or
//! another architecture, the two are the same work.

use criterion::Criterion;

pub const USES: &[&str] = &["dit", "hmac_sha256", "sha256"];

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
    use crate::{BenchDyn, OPENSSL, SIZES, VG};
    use criterion::{BenchmarkId, Throughput};
    use openssl::hash::MessageDigest;
    use openssl::pkey::PKey;
    use openssl::sign::Signer;
    use std::hint::black_box;
    use verified_garbage::dit;
    use verified_garbage::hashes::sha256::Sha256;
    use verified_garbage::hmac::Hmac;

    const PIECE: usize = 64;
    let key = [0x0b; 32];
    let pkey = PKey::hmac(&key).unwrap();
    let mac = |data: &[u8]| {
        let mut h = Hmac::<Sha256>::new(black_box(&key));
        for piece in data.chunks(PIECE) {
            h.update(black_box(piece));
        }
        h.finalize()
    };

    let mut g = c.benchmark_group("hmac-sha256-updates");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        assert_eq!(mac(&data), Hmac::<Sha256>::mac(&key, &data));
        g.bench(BenchmarkId::new(VG, size), |b| b.iter(|| mac(&data)));
        let mut out = [0u8; 32];
        g.bench(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Signer::new(MessageDigest::sha256(), &pkey).unwrap();
                for piece in data.chunks(PIECE) {
                    s.update(black_box(piece)).unwrap();
                }
                s.sign(&mut out).unwrap()
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("hmac-sha256-updates-dit-scope");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        assert_eq!(dit::scope(|| mac(&data)), Hmac::<Sha256>::mac(&key, &data));
        g.bench(BenchmarkId::new(VG, size), |b| {
            b.iter(|| dit::scope(|| mac(&data)))
        });
    }
    g.finish();
}
