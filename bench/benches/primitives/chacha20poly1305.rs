//! ChaCha20-Poly1305.

use criterion::Criterion;

pub const USES: &[&str] = &["chacha20poly1305", "chacha20", "poly1305"];

/// One-shot ChaCha20-Poly1305 encryption and decryption (key setup included),
/// with a 12-byte nonce and 16 bytes of associated data. This library's and
/// aws-lc-rs's run in place with a separate tag, OpenSSL's out of place; and
/// encryption out of place for all three, of a plaintext in two pieces as a
/// TLS 1.3 record's is (its payload and its content type, the last byte),
/// next to this library's copy of the pieces followed by encryption in
/// place, which `encrypt` should be no slower than.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::aead::{Aad, CHACHA20_POLY1305, LessSafeKey, Nonce, UnboundKey};
    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, decrypt_aead, encrypt_aead};
    use verified_garbage::chacha20poly1305::ChaCha20Poly1305;

    use crate::{AWS_LC, OPENSSL, VG};
    // The shared sizes, and more below 1 KiB and at 4 KiB, where the TLS
    // records of interactive traffic fall; and TLS 1.3's records of 512 and
    // 768 bytes, 1 KiB, 4 KiB and 16 KiB (the most a record carries) of
    // payload, whose plaintext is one byte longer: the content type; 320,
    // 384, 480 and 896 bytes, between them; and 1350 bytes, a record that
    // fills an Ethernet frame.
    const SIZES: [usize; 18] = [
        16, 64, 256, 320, 384, 480, 512, 513, 768, 769, 896, 1024, 1025, 1350, 4096, 4097, 16384,
        16385,
    ];
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

    // Out of place: from `data` and `content_type`, the last byte, into a
    // separate buffer.
    let mut g = c.benchmark_group("chacha20poly1305-encrypt-out-of-place");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0u8; size - 1];
        let content_type = [0x17u8];
        let mut out = crate::InPlace::new(size, &data);
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                ChaCha20Poly1305::new(black_box(&key))
                    .encrypt(
                        black_box(&nonce),
                        black_box(&aad),
                        &[black_box(&data[..]), black_box(&content_type[..])],
                        black_box(&mut out),
                    )
                    .unwrap()
            })
        });
        let whole = vec![0u8; size];
        let mut tag = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                encrypt_aead(
                    Cipher::chacha20_poly1305(),
                    black_box(&key),
                    Some(black_box(&nonce)),
                    black_box(&aad),
                    black_box(&whole),
                    &mut tag,
                )
                .unwrap()
            })
        });
        // aws-lc-rs takes the last piece as its `extra_in`, and writes its
        // encryption, before the tag, to `extra_out_and_tag`.
        let mut extra_out_and_tag = [0u8; 17];
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                aws_lc_key(black_box(&key))
                    .seal_out_of_place_scatter(
                        Nonce::assume_unique_for_key(*black_box(&nonce)),
                        Aad::from(black_box(&aad)),
                        black_box(&data),
                        black_box(&mut out[..size - 1]),
                        black_box(&content_type),
                        &mut extra_out_and_tag,
                    )
                    .unwrap()
            })
        });
    }
    g.finish();

    // The same, by copying the pieces into the output and encrypting it in
    // place.
    let mut g = c.benchmark_group("chacha20poly1305-copy-encrypt-in-place");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let data = vec![0u8; size - 1];
        let content_type = [0x17u8];
        let mut out = crate::InPlace::new(size, &data);
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let (body, last) = out.split_at_mut(size - 1);
                body.copy_from_slice(black_box(&data));
                last.copy_from_slice(black_box(&content_type));
                ChaCha20Poly1305::new(black_box(&key))
                    .encrypt_in_place(black_box(&nonce), black_box(&aad), black_box(&mut out))
                    .unwrap()
            })
        });
    }
    g.finish();

    tls_records(c);
}

/// TLS 1.3 records, as a TLS library seals and opens them with a key reused
/// for the connection: a 12-byte nonce and a record's 5 bytes of additional
/// data (the groups above have 16, which no TLS 1.3 record does); sealed out
/// of place from two pieces (the payload and its content type byte), and
/// opened in place, with the buffers where rustls puts them
/// (`aes_gcm::Offsets::DEFAULT`), as `aes-*-gcm-tls-seal` and `-open` are.
/// aws-lc-rs seals in place (the payload and the content type already in the
/// record buffer), and OpenSSL streams the pieces through one context. The
/// sizes are the records' plaintexts, the content type included: short
/// records (alerts, handshake messages, small requests) up to 192 bytes, and
/// the lengths around 193, 448 to 449 and 639 to 640 bytes.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn tls_records(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::aead::{Aad, CHACHA20_POLY1305, LessSafeKey, Nonce, UnboundKey};
    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher::Cipher as OsslCipher;
    use openssl::cipher_ctx::CipherCtx;
    use verified_garbage::chacha20poly1305::ChaCha20Poly1305;

    use crate::aes_gcm::{Aligned, Offsets};
    use crate::{AWS_LC, OPENSSL, VG};

    const TLS_SIZES: [usize; 10] = [16, 64, 128, 192, 193, 256, 448, 449, 639, 640];
    let offsets = Offsets::DEFAULT;
    let key = [0x42u8; 32];
    let nonce = [0x24; 12];
    let aad = Aligned::new(&[0x17, 0x03, 0x03, 0x40, 0x11], offsets.aad);
    let ty = [0x17u8];
    let vg_key = ChaCha20Poly1305::new(&key);
    let aws_lc_key = LessSafeKey::new(UnboundKey::new(&CHACHA20_POLY1305, &key).unwrap());
    let mut ossl = CipherCtx::new().unwrap();
    ossl.encrypt_init(Some(OsslCipher::chacha20_poly1305()), Some(&key), None)
        .unwrap();
    let mut ossl_dec = CipherCtx::new().unwrap();
    ossl_dec
        .decrypt_init(Some(OsslCipher::chacha20_poly1305()), Some(&key), None)
        .unwrap();
    for size in TLS_SIZES {
        let data = Aligned::new(&vec![0u8; size - 1], offsets.input);
        let mut out = Aligned::new(&vec![0u8; size], offsets.output);
        let mut t = [0u8; 16];
        let mut ossl_out = Aligned::new(&vec![0u8; size + 16], offsets.output);
        let tag = vg_key
            .encrypt(&nonce, &aad, &[&data, &ty], &mut out)
            .unwrap();
        let ct = Aligned::new(&out, offsets.input);
        let mut record = Aligned::new(&[&data[..], &ty].concat(), offsets.input);
        let aws_lc_tag = aws_lc_key
            .seal_in_place_separate_tag(
                Nonce::assume_unique_for_key(nonce),
                Aad::from(&aad[..]),
                &mut record,
            )
            .unwrap();
        assert_eq!((&record[..], aws_lc_tag.as_ref()), (&ct[..], &tag[..]));

        let mut g = c.benchmark_group("chacha20poly1305-tls-seal");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                vg_key
                    .encrypt(
                        black_box(&nonce),
                        black_box(&aad),
                        &[black_box(&data[..]), black_box(&ty[..])],
                        black_box(&mut out),
                    )
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                ossl.encrypt_init(None, None, Some(black_box(&nonce)))
                    .unwrap();
                ossl.cipher_update(black_box(&aad), None).unwrap();
                let n = ossl
                    .cipher_update(black_box(&data), Some(&mut ossl_out))
                    .unwrap();
                let n = n + ossl
                    .cipher_update(black_box(&ty), Some(&mut ossl_out[n..]))
                    .unwrap();
                ossl.cipher_final(&mut ossl_out[n..]).unwrap();
                ossl.tag(&mut t).unwrap();
                t
            })
        });
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                aws_lc_key
                    .seal_in_place_separate_tag(
                        Nonce::assume_unique_for_key(*black_box(&nonce)),
                        Aad::from(black_box(&aad)),
                        black_box(&mut record),
                    )
                    .unwrap()
            })
        });
        g.finish();

        // Each iteration opens the record again from its ciphertext.
        let mut buf = Aligned::new(&ct, offsets.input);
        let mut g = c.benchmark_group("chacha20poly1305-tls-open");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                buf.copy_from_slice(&ct);
                vg_key
                    .decrypt_in_place(
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
                ossl_dec
                    .decrypt_init(None, None, Some(black_box(&nonce)))
                    .unwrap();
                ossl_dec.cipher_update(black_box(&aad), None).unwrap();
                let n = ossl_dec
                    .cipher_update(black_box(&ct), Some(&mut ossl_out))
                    .unwrap();
                ossl_dec.set_tag(&tag).unwrap();
                ossl_dec.cipher_final(&mut ossl_out[n..]).unwrap();
            })
        });
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                buf.copy_from_slice(&ct);
                aws_lc_key
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
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
