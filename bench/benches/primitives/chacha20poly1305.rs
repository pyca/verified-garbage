//! ChaCha20-Poly1305.

use criterion::Criterion;

pub const USES: &[&str] = &["chacha20poly1305", "chacha20", "poly1305"];

/// One-shot ChaCha20-Poly1305 encryption and decryption (key setup included),
/// with a 12-byte nonce and 16 bytes of associated data. This library's and
/// aws-lc-rs's run in place with a separate tag, OpenSSL's out of place.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::aead::{Aad, CHACHA20_POLY1305, LessSafeKey, Nonce, UnboundKey};
    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode, decrypt_aead, encrypt_aead};
    use verified_garbage::chacha20poly1305::ChaCha20Poly1305;

    use crate::{AWS_LC, OPENSSL, SIZES, VG};
    let key = [0x42; 32];
    let nonce = [0x24; 12];
    let aad = [0x11; 16];
    let aws_lc_key =
        |key: &[u8]| LessSafeKey::new(UnboundKey::new(&CHACHA20_POLY1305, key).unwrap());
    let mut g = c.benchmark_group("chacha20poly1305");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let mut data = vec![0u8; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                ChaCha20Poly1305::new(black_box(&key))
                    .encrypt_in_place(black_box(&nonce), black_box(&aad), black_box(&mut data))
                    .unwrap()
            })
        });
        let mut tag = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                encrypt_aead(
                    Cipher::chacha20_poly1305(),
                    black_box(&key),
                    Some(black_box(&nonce)),
                    black_box(&aad),
                    black_box(&data),
                    &mut tag,
                )
                .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                aws_lc_key(black_box(&key))
                    .seal_in_place_separate_tag(
                        Nonce::assume_unique_for_key(*black_box(&nonce)),
                        Aad::from(black_box(&aad)),
                        black_box(&mut data),
                    )
                    .unwrap()
            })
        });
    }
    g.finish();

    // Out of place, shaped as a TLS 1.3 record: the plaintext and the
    // content-type byte after it encrypted into a separate buffer, as
    // rustls's record layer asks of its provider (aws-lc-rs's
    // `seal_out_of_place_scatter` with the byte as `extra_in`; OpenSSL's
    // EVP interface always encrypts out of place).
    let typ = [0x17u8];
    let mut g = c.benchmark_group("chacha20poly1305-out-of-place");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0u8; size];
        let mut out = vec![0u8; size + 1];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                ChaCha20Poly1305::new(black_box(&key))
                    .encrypt(
                        black_box(&nonce),
                        black_box(&aad),
                        &[black_box(&data[..]), &typ],
                        black_box(&mut out),
                    )
                    .unwrap()
            })
        });
        let mut ossl_out = vec![0u8; size + 1];
        let mut tag = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Crypter::new(
                    Cipher::chacha20_poly1305(),
                    Mode::Encrypt,
                    black_box(&key),
                    Some(black_box(&nonce)),
                )
                .unwrap();
                s.aad_update(black_box(&aad)).unwrap();
                let n = s.update(black_box(&data), &mut ossl_out).unwrap();
                let n = n + s.update(&typ, &mut ossl_out[n..]).unwrap();
                s.finalize(&mut ossl_out[n..]).unwrap();
                s.get_tag(&mut tag).unwrap();
            })
        });
        let mut extra = [0u8; 17];
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                aws_lc_key(black_box(&key))
                    .seal_out_of_place_scatter(
                        Nonce::assume_unique_for_key(*black_box(&nonce)),
                        Aad::from(black_box(&aad)),
                        black_box(&data),
                        black_box(&mut out[..size]),
                        &typ,
                        &mut extra,
                    )
                    .unwrap()
            })
        });
    }
    g.finish();

    let mut g = c.benchmark_group("chacha20poly1305-decrypt");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let mut ciphertext = vec![0u8; size];
        let tag = ChaCha20Poly1305::new(&key)
            .encrypt_in_place(&nonce, &aad, &mut ciphertext)
            .unwrap();
        let mut data = ciphertext.clone();
        let mut aws_lc_ct = vec![0u8; size];
        let aws_lc_tag = aws_lc_key(&key)
            .seal_in_place_separate_tag(
                Nonce::assume_unique_for_key(nonce),
                Aad::from(aad),
                &mut aws_lc_ct,
            )
            .unwrap();
        assert_eq!((&aws_lc_ct, aws_lc_tag.as_ref()), (&ciphertext, &tag[..]));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                data.copy_from_slice(&ciphertext);
                ChaCha20Poly1305::new(black_box(&key))
                    .decrypt_in_place(
                        black_box(&nonce),
                        black_box(&aad),
                        black_box(&mut data),
                        black_box(&tag),
                    )
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                decrypt_aead(
                    Cipher::chacha20_poly1305(),
                    black_box(&key),
                    Some(black_box(&nonce)),
                    black_box(&aad),
                    black_box(&ciphertext),
                    black_box(&tag),
                )
                .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                data.copy_from_slice(&ciphertext);
                aws_lc_key(black_box(&key))
                    .open_in_place_separate_tag(
                        Nonce::assume_unique_for_key(*black_box(&nonce)),
                        Aad::from(black_box(&aad)),
                        black_box(&tag),
                        black_box(&mut data),
                    )
                    .unwrap();
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
