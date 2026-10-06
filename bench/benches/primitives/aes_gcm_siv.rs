//! AES-GCM-SIV.
//!
//! OpenSSL implements AES-GCM-SIV from version 3.2, which the runners'
//! OpenSSL (3.0) predates, so there is nothing of OpenSSL's to compare with:
//! these compare this library with aws-lc-rs alone.

use criterion::Criterion;

pub const USES: &[&str] = &["aes_gcm_siv", "aes_gcm", "aes", "gcm"];

/// One-shot AEAD_AES_128_GCM_SIV encryption and decryption (key setup
/// included), with 16 bytes of associated data, in place with a separate tag
/// in both libraries.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::aead::{AES_128_GCM_SIV, Aad, LessSafeKey, Nonce, UnboundKey};
    use criterion::{BenchmarkId, Throughput};
    use verified_garbage::aes_gcm_siv::AesGcmSiv;

    use crate::{AWS_LC, SIZES, VG};

    let key = [0x42; 16];
    let nonce = [0x24; 12];
    let aad = [0x5a; 16];
    let aws_lc_key = |key: &[u8]| LessSafeKey::new(UnboundKey::new(&AES_128_GCM_SIV, key).unwrap());
    for size in SIZES {
        let mut buf = vec![0u8; size];
        let tag = AesGcmSiv::new(&key)
            .unwrap()
            .encrypt_in_place(&nonce, &aad, &mut buf)
            .unwrap();
        let ct = buf.clone();
        let mut aws_lc_ct = vec![0u8; size];
        let aws_lc_tag = aws_lc_key(&key)
            .seal_in_place_separate_tag(
                Nonce::assume_unique_for_key(nonce),
                Aad::from(aad),
                &mut aws_lc_ct,
            )
            .unwrap();
        assert_eq!((&aws_lc_ct, aws_lc_tag.as_ref()), (&ct, &tag[..]));

        let mut g = c.benchmark_group("aes-128-gcm-siv-encrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let k = AesGcmSiv::new(black_box(&key)).unwrap();
                k.encrypt_in_place(black_box(&nonce), black_box(&aad), black_box(&mut buf))
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                aws_lc_key(black_box(&key))
                    .seal_in_place_separate_tag(
                        Nonce::assume_unique_for_key(*black_box(&nonce)),
                        Aad::from(black_box(&aad)),
                        black_box(&mut buf),
                    )
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
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                buf.copy_from_slice(&ct);
                aws_lc_key(black_box(&key))
                    .open_in_place_separate_tag(
                        Nonce::assume_unique_for_key(*black_box(&nonce)),
                        Aad::from(black_box(&aad)),
                        &tag,
                        black_box(&mut buf),
                    )
                    .unwrap();
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
