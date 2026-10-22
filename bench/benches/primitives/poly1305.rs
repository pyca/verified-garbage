//! Poly1305.

use criterion::Criterion;

pub const USES: &[&str] = &["poly1305"];

// aws-lc-rs has no public Poly1305 (only ChaCha20-Poly1305), so there is no
// aws-lc-rs entry.

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::pkey::{Id, PKey};
    use openssl::sign::Signer;
    use verified_garbage::poly1305::Poly1305;

    use crate::{OPENSSL, VG};
    // The shared sizes, and TLS 1.3's records of 1 KiB and 4 KiB of payload,
    // whose plaintext is one byte longer (the content type): a partial last
    // block, which ChaCha20-Poly1305 authenticates at these sizes too; and
    // 480 bytes (30 blocks), near where the x86-64 IFMA code hands short
    // inputs to other code.
    const SIZES: [usize; 11] = [64, 128, 192, 256, 320, 384, 448, 480, 1024, 1025, 4097];
    let key = [0x0b; 32];
    let mut g = c.benchmark_group("poly1305");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| Poly1305::mac(black_box(&key), black_box(&data)))
        });
        let mut out = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let pkey = PKey::private_key_from_raw_bytes(black_box(&key), Id::POLY1305).unwrap();
                let mut s = Signer::new_without_digest(&pkey).unwrap();
                s.sign_oneshot(&mut out, black_box(&data)).unwrap()
            })
        });
        // Diagnostic: AWS-LC's own Poly1305.
        #[cfg(target_arch = "x86_64")]
        g.bench_function(BenchmarkId::new(crate::AWS_LC, size), |b| {
            b.iter(|| unsafe {
                let mut st: aws_lc_sys::poly1305_state = [0; 512];
                let mut mac = [0u8; 16];
                aws_lc_sys::CRYPTO_poly1305_init(&mut st, black_box(key.as_ptr()));
                aws_lc_sys::CRYPTO_poly1305_update(&mut st, black_box(data.as_ptr()), size);
                aws_lc_sys::CRYPTO_poly1305_finish(&mut st, mac.as_mut_ptr());
                mac
            })
        });
    }
    g.finish();

    let pkey = PKey::private_key_from_raw_bytes(&key, Id::POLY1305).unwrap();
    let mut g = c.benchmark_group("poly1305-verify");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0x5a; size];
        let tag = Poly1305::mac(&key, &data);
        let mut reference = [0; 16];
        let mut signer = Signer::new_without_digest(&pkey).unwrap();
        assert_eq!(signer.sign_oneshot(&mut reference, &data).unwrap(), 16);
        assert_eq!(reference, tag);
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut p = Poly1305::new(black_box(&key));
                p.update(black_box(&data));
                p.verify(black_box(&tag)).unwrap()
            })
        });
        let mut out = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let pkey = PKey::private_key_from_raw_bytes(black_box(&key), Id::POLY1305).unwrap();
                let mut s = Signer::new_without_digest(&pkey).unwrap();
                let n = s.sign_oneshot(&mut out, black_box(&data)).unwrap();
                assert!(openssl::memcmp::eq(&out[..n], black_box(&tag)))
            })
        });
    }
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
