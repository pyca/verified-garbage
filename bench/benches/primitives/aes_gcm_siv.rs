//! AES-GCM-SIV.
//!
//! Enable `openssl-gcm-siv` with OpenSSL 3.2+ (including 4.x) to compare
//! all three libraries in place, with a separate tag and key setup included.

use criterion::Criterion;

pub const USES: &[&str] = &["aes_gcm_siv", "aes_gcm", "aes", "gcm"];

/// One-shot AES-128/256-GCM-SIV encryption and decryption (key setup
/// included), with 16 bytes of associated data, in place with a separate tag
/// in every library. Cipher fetching is outside the timed OpenSSL operation.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::aead::{AES_128_GCM_SIV, AES_256_GCM_SIV, Aad, LessSafeKey, Nonce, UnboundKey};
    use criterion::{BenchmarkId, Throughput};
    use verified_garbage::aes_gcm_siv::AesGcmSiv;

    use crate::{AWS_LC, BenchDyn, SIZES, VG};

    for (key_len, algorithm) in [(16, &AES_128_GCM_SIV), (32, &AES_256_GCM_SIV)] {
        let key = vec![0x42; key_len];
        #[cfg(feature = "openssl-gcm-siv")]
        let cipher =
            openssl::cipher::Cipher::fetch(None, &format!("AES-{}-GCM-SIV", key_len * 8), None)
                .unwrap();
        let nonce = [0x24; 12];
        let aad = [0x5a; 16];
        let aws_lc_key = |key: &[u8]| LessSafeKey::new(UnboundKey::new(algorithm, key).unwrap());
        for size in SIZES.into_iter().chain([1048576]) {
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

            let mut g = c.benchmark_group(format!("aes-{}-gcm-siv-encrypt", key_len * 8));
            g.throughput(Throughput::Bytes(size as u64));
            g.bench(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    let k = AesGcmSiv::new(black_box(&key)).unwrap();
                    k.encrypt_in_place(black_box(&nonce), black_box(&aad), black_box(&mut buf))
                        .unwrap()
                })
            });
            g.bench(BenchmarkId::new(AWS_LC, size), |b| {
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
            #[cfg(feature = "openssl-gcm-siv")]
            {
                let mut expected = vec![0; size];
                let expected_tag =
                    openssl_gcm_siv::seal(&cipher, &key, &nonce, &aad, &mut expected);
                assert_eq!((&expected, expected_tag), (&ct, tag));
                g.bench(BenchmarkId::new(crate::OPENSSL, size), |b| {
                    b.iter(|| {
                        openssl_gcm_siv::seal(
                            &cipher,
                            black_box(&key),
                            black_box(&nonce),
                            black_box(&aad),
                            black_box(&mut buf),
                        )
                    })
                });
            }
            g.finish();

            let mut g = c.benchmark_group(format!("aes-{}-gcm-siv-decrypt", key_len * 8));
            g.throughput(Throughput::Bytes(size as u64));
            g.bench(BenchmarkId::new(VG, size), |b| {
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
            g.bench(BenchmarkId::new(AWS_LC, size), |b| {
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
            #[cfg(feature = "openssl-gcm-siv")]
            {
                let mut expected = ct.clone();
                openssl_gcm_siv::open(&cipher, &key, &nonce, &aad, &mut expected, &tag).unwrap();
                assert_eq!(expected, vec![0; size]);
                g.bench(BenchmarkId::new(crate::OPENSSL, size), |b| {
                    b.iter(|| {
                        buf.copy_from_slice(&ct);
                        openssl_gcm_siv::open(
                            &cipher,
                            black_box(&key),
                            black_box(&nonce),
                            black_box(&aad),
                            black_box(&mut buf),
                            black_box(&tag),
                        )
                        .unwrap();
                    })
                });
            }
            g.finish();
        }
    }
}

#[cfg(feature = "openssl-gcm-siv")]
#[path = "../../support/openssl_gcm_siv.rs"]
mod openssl_gcm_siv;

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
