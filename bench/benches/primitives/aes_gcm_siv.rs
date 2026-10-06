//! AES-GCM-SIV.
//!
//! OpenSSL implements AES-GCM-SIV from version 3.2, which the runners'
//! OpenSSL (3.0) predates, so there is nothing of OpenSSL's to compare with:
//! these benchmark this library alone.

use criterion::Criterion;

pub const USES: &[&str] = &["aes_gcm_siv", "aes_gcm", "aes", "gcm"];

/// One-shot AEAD_AES_128_GCM_SIV encryption and decryption (key setup
/// included), with 16 bytes of associated data.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use verified_garbage::aes_gcm_siv::AesGcmSiv;

    use crate::{SIZES, VG};

    let key = [0x42; 16];
    let nonce = [0x24; 12];
    let aad = [0x5a; 16];
    for size in SIZES {
        let mut buf = vec![0u8; size];
        let tag = AesGcmSiv::new(&key)
            .unwrap()
            .encrypt_in_place(&nonce, &aad, &mut buf)
            .unwrap();
        let ct = buf.clone();

        let mut g = c.benchmark_group("aes-128-gcm-siv-encrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let k = AesGcmSiv::new(black_box(&key)).unwrap();
                k.encrypt_in_place(black_box(&nonce), black_box(&aad), black_box(&mut buf))
                    .unwrap()
            })
        });
        g.finish();

        let mut g = c.benchmark_group("aes-128-gcm-siv-decrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                buf.copy_from_slice(&ct);
                let k = AesGcmSiv::new(black_box(&key)).unwrap();
                k.decrypt_in_place(
                    black_box(&nonce),
                    black_box(&aad),
                    black_box(&mut buf),
                    &tag,
                )
                .unwrap()
            })
        });
        g.finish();
    }
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
)))]
pub fn bench(_: &mut Criterion) {}
