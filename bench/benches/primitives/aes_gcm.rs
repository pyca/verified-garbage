//! AES-GCM.

use criterion::Criterion;

pub const USES: &[&str] = &["aes_gcm", "aes", "gcm"];

/// One-shot AES-GCM encryption and decryption (setup included), and
/// streaming encryption, with a 16-byte key, a 12-byte nonce and 16 bytes of
/// additional data. aws-lc-rs, which has no streaming AES-GCM, is measured
/// one-shot only, in place with a separate tag as this library's is. The
/// one-shot functions are also measured at `RECORD_SIZES`, the short
/// messages of protocols such as TLS and QUIC, where the fixed costs of a
/// call (the hash subkey's powers, the tag) weigh the most.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::aead::{AES_128_GCM, Aad, LessSafeKey, Nonce, UnboundKey};
    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode, decrypt_aead, encrypt_aead};
    use verified_garbage::aes_gcm::AesGcm;

    use crate::{AWS_LC, OPENSSL, SIZES, VG};

    /// The sizes measured one-shot only, besides `SIZES`.
    const RECORD_SIZES: [usize; 3] = [128, 192, 384];

    let key = [0x42; 16];
    let nonce = [0x24; 12];
    let aad = [0x5a; 16];
    let cipher = Cipher::aes_128_gcm();
    let aws_lc_key = |key: &[u8]| LessSafeKey::new(UnboundKey::new(&AES_128_GCM, key).unwrap());
    let mut sizes = [SIZES.as_slice(), RECORD_SIZES.as_slice()].concat();
    sizes.sort_unstable();
    for size in sizes {
        let data = vec![0u8; size];
        let mut buf = data.clone();
        let tag = AesGcm::new(&key)
            .unwrap()
            .encrypt_in_place(&nonce, &aad, &mut buf)
            .unwrap();
        let ct = buf.clone();
        let mut aws_lc_ct = data.clone();
        let aws_lc_tag = aws_lc_key(&key)
            .seal_in_place_separate_tag(
                Nonce::assume_unique_for_key(nonce),
                Aad::from(aad),
                &mut aws_lc_ct,
            )
            .unwrap();
        assert_eq!((&aws_lc_ct, aws_lc_tag.as_ref()), (&ct, &tag[..]));

        let mut g = c.benchmark_group("aes-128-gcm-encrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let k = AesGcm::new(black_box(&key)).unwrap();
                k.encrypt_in_place(black_box(&nonce), black_box(&aad), black_box(&mut buf))
                    .unwrap()
            })
        });
        let mut t = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                encrypt_aead(
                    cipher,
                    black_box(&key),
                    Some(black_box(&nonce)),
                    black_box(&aad),
                    black_box(&data),
                    &mut t,
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
                        black_box(&mut buf),
                    )
                    .unwrap()
            })
        });
        g.finish();

        // Out of place, shaped as a TLS 1.3 record: the plaintext and the
        // content-type byte after it encrypted into a separate buffer, as
        // rustls's record layer asks of its provider (aws-lc-rs's
        // `seal_out_of_place_scatter` with the byte as `extra_in`).
        let typ = [0x17u8];
        let mut out = vec![0u8; size + 1];
        let mut extra = [0u8; 17];
        let mut g = c.benchmark_group("aes-128-gcm-encrypt-out-of-place");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let k = AesGcm::new(black_box(&key)).unwrap();
                k.encrypt(
                    black_box(&nonce),
                    black_box(&aad),
                    &[black_box(&data[..]), &typ],
                    black_box(&mut out),
                )
                .unwrap()
            })
        });
        let mut ossl_out = vec![0u8; size + 1 + cipher.block_size()];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Crypter::new(
                    cipher,
                    Mode::Encrypt,
                    black_box(&key),
                    Some(black_box(&nonce)),
                )
                .unwrap();
                s.aad_update(black_box(&aad)).unwrap();
                let n = s.update(black_box(&data), &mut ossl_out).unwrap();
                let n = n + s.update(&typ, &mut ossl_out[n..]).unwrap();
                s.finalize(&mut ossl_out[n..]).unwrap();
                s.get_tag(&mut t).unwrap();
            })
        });
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
        g.finish();

        let mut g = c.benchmark_group("aes-128-gcm-decrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                buf.copy_from_slice(&ct);
                let k = AesGcm::new(black_box(&key)).unwrap();
                k.decrypt_in_place(
                    black_box(&nonce),
                    black_box(&aad),
                    black_box(&mut buf),
                    &tag,
                )
                .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                decrypt_aead(
                    cipher,
                    black_box(&key),
                    Some(black_box(&nonce)),
                    black_box(&aad),
                    black_box(&ct),
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

        if !SIZES.contains(&size) {
            continue;
        }
        let mut g = c.benchmark_group("aes-128-gcm-stream");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let k = AesGcm::new(black_box(&key)).unwrap();
                let mut s = k.encryptor(black_box(&nonce)).unwrap();
                s.update_aad(black_box(&aad)).unwrap();
                s.update(black_box(&mut buf)).unwrap();
                s.finalize()
            })
        });
        let mut out = vec![0u8; size + cipher.block_size()];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut s = Crypter::new(
                    cipher,
                    Mode::Encrypt,
                    black_box(&key),
                    Some(black_box(&nonce)),
                )
                .unwrap();
                s.aad_update(black_box(&aad)).unwrap();
                let n = s.update(black_box(&data), &mut out).unwrap();
                s.finalize(&mut out[n..]).unwrap();
                s.get_tag(&mut t).unwrap();
            })
        });
        g.finish();
    }

    // Small streaming fragments reuse the partial-block keystream: they
    // should not repeatedly enter the whole-block counter-mode primitive.
    let size = 64;
    let data = vec![0u8; size];
    let mut buf = data.clone();
    let mut out = [0u8; 32];
    let mut tag = [0u8; 16];
    let mut g = c.benchmark_group("aes-128-gcm-stream-bytes");
    g.throughput(Throughput::Bytes(size as u64));
    g.bench_function(BenchmarkId::new(VG, size), |b| {
        b.iter(|| {
            let k = AesGcm::new(black_box(&key)).unwrap();
            let mut s = k.encryptor(black_box(&nonce)).unwrap();
            s.update_aad(black_box(&aad)).unwrap();
            for byte in buf.chunks_mut(1) {
                s.update(black_box(byte)).unwrap();
            }
            s.finalize()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
        b.iter(|| {
            let mut s = Crypter::new(
                cipher,
                Mode::Encrypt,
                black_box(&key),
                Some(black_box(&nonce)),
            )
            .unwrap();
            s.aad_update(black_box(&aad)).unwrap();
            for byte in data.chunks(1) {
                s.update(black_box(byte), &mut out).unwrap();
            }
            s.finalize(&mut out).unwrap();
            s.get_tag(&mut tag).unwrap();
        })
    });
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}
