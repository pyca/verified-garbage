//! AES-GCM.

use criterion::Criterion;

pub const USES: &[&str] = &["aes_gcm", "aes", "gcm"];

/// One-shot AES-GCM encryption (in place, and out of place from one piece
/// and from two: a TLS 1.3 record's payload and its content type byte) and
/// decryption (setup included), and streaming encryption, with a 16-byte
/// key, a 12-byte nonce and 16 bytes of additional data. aws-lc-rs, which
/// has no streaming AES-GCM, is measured one-shot only, with a separate tag
/// as this library's is. The one-shot functions are also measured at `RECORD_SIZES`, the short
/// messages of protocols such as TLS and QUIC, where the fixed costs of a
/// call (the key's setup, the tag) weigh the most. Encryption with a key
/// used for many messages, as a TLS or QUIC connection's is, is also
/// measured at `REUSED_SIZES`, which are not multiples of 16 blocks (also
/// out of place from two halves, whose second holds whole blocks).
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

    use aws_lc_rs::aead::{AES_128_GCM, Aad, LessSafeKey, Nonce, UnboundKey};
    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher::Cipher as OsslCipher;
    use openssl::cipher_ctx::CipherCtx;
    use openssl::symm::{Cipher, Crypter, Mode, decrypt_aead, encrypt_aead};
    use verified_garbage::aes_gcm::AesGcm;

    use crate::{AWS_LC, OPENSSL, SIZES, VG};

    /// The sizes measured one-shot only, besides `SIZES`.
    const RECORD_SIZES: [usize; 3] = [128, 192, 384];
    /// The sizes measured with a key reused across messages.
    const REUSED_SIZES: [usize; 3] = [600, 1350, 4000];

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

        // Out of place: from `data` into a separate buffer.
        let mut out = vec![0u8; size];
        let mut ossl_out = vec![0u8; size + cipher.block_size()];
        let mut aws_lc_tag = [0u8; 16];
        let mut g = c.benchmark_group("aes-128-gcm-encrypt-out-of-place");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let k = AesGcm::new(black_box(&key)).unwrap();
                k.encrypt(
                    black_box(&nonce),
                    black_box(&aad),
                    &[black_box(&data[..])],
                    black_box(&mut out),
                )
                .unwrap()
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
                let n = s.update(black_box(&data), &mut ossl_out).unwrap();
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
                        black_box(&mut out),
                        &[],
                        &mut aws_lc_tag,
                    )
                    .unwrap()
            })
        });
        g.finish();

        // Out of place from two pieces, `data` and one more byte: a TLS 1.3
        // record, whose payload is followed by its content type.
        let ty = [0x17u8];
        let mut out = vec![0u8; size + 1];
        let mut aws_lc_out = vec![0u8; size];
        let mut aws_lc_extra = [0u8; 1 + 16];
        let pieces_tag = AesGcm::new(&key)
            .unwrap()
            .encrypt(&nonce, &aad, &[&data, &ty], &mut out)
            .unwrap();
        aws_lc_key(&key)
            .seal_out_of_place_scatter(
                Nonce::assume_unique_for_key(nonce),
                Aad::from(aad),
                &data,
                &mut aws_lc_out,
                &ty,
                &mut aws_lc_extra,
            )
            .unwrap();
        assert_eq!(
            (
                [&aws_lc_out[..], &aws_lc_extra[..1]].concat(),
                &aws_lc_extra[1..]
            ),
            (out.clone(), &pieces_tag[..])
        );
        let mut g = c.benchmark_group("aes-128-gcm-encrypt-two-pieces");
        g.throughput(Throughput::Bytes(size as u64 + 1));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let k = AesGcm::new(black_box(&key)).unwrap();
                k.encrypt(
                    black_box(&nonce),
                    black_box(&aad),
                    &[black_box(&data[..]), black_box(&ty[..])],
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
                let n = n + s.update(black_box(&ty), &mut ossl_out[n..]).unwrap();
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
                        black_box(&mut aws_lc_out),
                        black_box(&ty),
                        &mut aws_lc_extra,
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

    // A key reused for every message: in place, and out of place from two
    // pieces (a TLS 1.3 record's payload and its content type), each next to
    // OpenSSL's context and aws-lc-rs's key, also set up once.
    let vg_key = AesGcm::new(&key).unwrap();
    let aws_lc_reused = aws_lc_key(&key);
    let mut ossl = CipherCtx::new().unwrap();
    ossl.encrypt_init(Some(OsslCipher::aes_128_gcm()), Some(&key), None)
        .unwrap();
    let ty = [0x17u8];
    for size in REUSED_SIZES {
        let data = vec![0u8; size];
        let mut buf = data.clone();
        let mut ossl_out = vec![0u8; size + 1 + 16];
        let mut t = [0u8; 16];
        let mut ossl_seal = |pieces: &[&[u8]], out: &mut [u8]| {
            ossl.encrypt_init(None, None, Some(&nonce)).unwrap();
            ossl.cipher_update(&aad, None).unwrap();
            let mut n = 0;
            for p in pieces {
                n += ossl.cipher_update(p, Some(&mut out[n..])).unwrap();
            }
            ossl.cipher_final(&mut out[n..]).unwrap();
            ossl.tag(&mut t).unwrap();
            t
        };

        let tag = vg_key.encrypt_in_place(&nonce, &aad, &mut buf).unwrap();
        let ossl_tag = ossl_seal(&[&data], &mut ossl_out);
        assert_eq!((&buf[..], &tag[..]), (&ossl_out[..size], &ossl_tag[..]));
        let mut g = c.benchmark_group("aes-128-gcm-encrypt-reused-key");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                vg_key
                    .encrypt_in_place(black_box(&nonce), black_box(&aad), black_box(&mut buf))
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| ossl_seal(&[black_box(&data)], &mut ossl_out))
        });
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                aws_lc_reused
                    .seal_in_place_separate_tag(
                        Nonce::assume_unique_for_key(*black_box(&nonce)),
                        Aad::from(black_box(&aad)),
                        black_box(&mut buf),
                    )
                    .unwrap()
            })
        });
        g.finish();

        let mut out = vec![0u8; size + 1];
        let mut aws_lc_out = vec![0u8; size];
        let mut aws_lc_extra = [0u8; 1 + 16];
        let tag = vg_key
            .encrypt(&nonce, &aad, &[&data, &ty], &mut out)
            .unwrap();
        let ossl_tag = ossl_seal(&[&data, &ty], &mut ossl_out);
        assert_eq!((&out[..], &tag[..]), (&ossl_out[..size + 1], &ossl_tag[..]));
        let mut g = c.benchmark_group("aes-128-gcm-encrypt-two-pieces-reused-key");
        g.throughput(Throughput::Bytes(size as u64 + 1));
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
            b.iter(|| ossl_seal(&[black_box(&data), black_box(&ty)], &mut ossl_out))
        });
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                aws_lc_reused
                    .seal_out_of_place_scatter(
                        Nonce::assume_unique_for_key(*black_box(&nonce)),
                        Aad::from(black_box(&aad)),
                        black_box(&data),
                        black_box(&mut aws_lc_out),
                        black_box(&ty),
                        &mut aws_lc_extra,
                    )
                    .unwrap()
            })
        });
        g.finish();

        // Two halves, so that whole blocks follow the first piece.
        let (h1, h2) = data.split_at(size / 2);
        let mut out = vec![0u8; size];
        let mut aws_lc_out = vec![0u8; h1.len()];
        let mut aws_lc_extra = vec![0u8; h2.len() + 16];
        let tag = vg_key.encrypt(&nonce, &aad, &[h1, h2], &mut out).unwrap();
        let ossl_tag = ossl_seal(&[h1, h2], &mut ossl_out);
        assert_eq!((&out[..], &tag[..]), (&ossl_out[..size], &ossl_tag[..]));
        let mut g = c.benchmark_group("aes-128-gcm-encrypt-halves-reused-key");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                vg_key
                    .encrypt(
                        black_box(&nonce),
                        black_box(&aad),
                        &[black_box(h1), black_box(h2)],
                        black_box(&mut out),
                    )
                    .unwrap()
            })
        });
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| ossl_seal(&[black_box(h1), black_box(h2)], &mut ossl_out))
        });
        g.bench_function(BenchmarkId::new(AWS_LC, size), |b| {
            b.iter(|| {
                aws_lc_reused
                    .seal_out_of_place_scatter(
                        Nonce::assume_unique_for_key(*black_box(&nonce)),
                        Aad::from(black_box(&aad)),
                        black_box(h1),
                        black_box(&mut aws_lc_out),
                        black_box(h2),
                        &mut aws_lc_extra,
                    )
                    .unwrap()
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
    tls_records(c);
}

/// TLS records, as a TLS library seals and opens them with a key reused for
/// the connection: AES-128-GCM and AES-256-GCM, a 12-byte nonce and a TLS 1.3
/// record's 5 bytes of additional data; sealed out of place from two pieces
/// (the payload and its content type byte), and opened in place. aws-lc-rs
/// seals in place (the payload and the content type already in the record
/// buffer), and OpenSSL streams the pieces through one context. A
/// connection's records are also measured from its key's setup on
/// (`aes-*-gcm-tls-connection`, of 1, 2, 4 and 16 records), so that the cost
/// of a key used for a few records is counted too.
///
/// Each record's buffers sit at fixed offsets from a 4 KiB boundary
/// (`Offsets::DEFAULT`, where rustls puts them), the same at every size and
/// in every build: where an
/// allocator puts them otherwise depends on what was allocated before, and
/// moves some sizes' times by several percent on some cores (Apple's).
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn tls_records(c: &mut Criterion) {
    /// The payloads: a full record, a common web record, and smaller ones,
    /// each next to sizes that are not a multiple of 16 (as most records'
    /// are), since the end of a record costs differently from its blocks;
    /// and records of 16, 32, 48, 64 and 255 bytes with their content type
    /// (alerts, handshake messages, small requests); records of 112 to 240
    /// bytes with their content type, fewer than 16 blocks; a 2048-byte
    /// record; and records of 288, 416, 432 and 448 bytes of text.
    const TLS_SIZES: [usize; 29] = [
        15, 31, 47, 63, 111, 127, 207, 239, 254, 255, 256, 257, 287, 415, 431, 447, 1023, 1024,
        1025, 2047, 4095, 4096, 4097, 9999, 10000, 10001, 16383, 16384, 16385,
    ];

    tls_record_rows(c, &TLS_SIZES, Offsets::DEFAULT, "");
    tls_connection_rows(c);
    key_setup_rows(c);
}

/// Where a record's buffers start, in bytes past a 4 KiB boundary: the
/// plaintext the record is sealed from (and the record opened in place, or
/// sealed in place by aws-lc-rs), the ciphertext sealed into, and the
/// additional data.
#[derive(Clone, Copy)]
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub(crate) struct Offsets {
    pub(crate) input: usize,
    pub(crate) output: usize,
    pub(crate) aad: usize,
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl Offsets {
    /// The rows' offsets: where rustls puts a record's payload, 5 bytes (the
    /// TLS record header) past the start of an allocation (`PrefixedPayload`,
    /// sealed in place; and the first record in the receive buffer,
    /// `DeframerIter`, opened in place), and the output half a page from the
    /// input, so that sealing out of place never loads and stores at the same
    /// address modulo 4 KiB.
    pub(crate) const DEFAULT: Offsets = Offsets {
        input: 5,
        output: 2048 + 5,
        aad: 0,
    };
}

/// A copy of some bytes at a given offset past a 4 KiB boundary.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub(crate) struct Aligned {
    raw: Vec<u8>,
    start: usize,
    len: usize,
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl Aligned {
    pub(crate) fn new(bytes: &[u8], offset: usize) -> Self {
        let raw = vec![0u8; bytes.len() + offset + 4096];
        let start = raw.as_ptr().align_offset(4096) + offset;
        let mut a = Aligned {
            raw,
            start,
            len: bytes.len(),
        };
        a.copy_from_slice(bytes);
        a
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl std::ops::Deref for Aligned {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.raw[self.start..self.start + self.len]
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl std::ops::DerefMut for Aligned {
    fn deref_mut(&mut self) -> &mut [u8] {
        &mut self.raw[self.start..self.start + self.len]
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl AsRef<[u8]> for Aligned {
    fn as_ref(&self) -> &[u8] {
        self
    }
}

/// Sealing and opening one record of each of `sizes` bytes, with the
/// buffers at `offsets` (each group's name ends with `label`).
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn tls_record_rows(c: &mut Criterion, sizes: &[usize], offsets: Offsets, label: &str) {
    use std::hint::black_box;

    use aws_lc_rs::aead::{AES_128_GCM, AES_256_GCM, Aad, LessSafeKey, Nonce, UnboundKey};
    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher::Cipher as OsslCipher;
    use openssl::cipher_ctx::CipherCtx;
    use verified_garbage::aes_gcm::AesGcm;

    use crate::{AWS_LC, OPENSSL, VG};

    let nonce = [0x24; 12];
    let aad = Aligned::new(&[0x17, 0x03, 0x03, 0x40, 0x11], offsets.aad);
    let ty = [0x17u8];
    for (bits, key) in [(128, &[0x42u8; 16][..]), (256, &[0x42u8; 32][..])] {
        let (alg, ossl_alg) = if bits == 128 {
            (&AES_128_GCM, OsslCipher::aes_128_gcm())
        } else {
            (&AES_256_GCM, OsslCipher::aes_256_gcm())
        };
        let vg_key = AesGcm::new(key).unwrap();
        // A connection's key has sealed and opened many records before its
        // short ones: seal long records with it first, as a connection has.
        let mut warm = vec![0u8; 1024];
        for _ in 0..64 {
            vg_key.encrypt_in_place(&nonce, &aad, &mut warm).unwrap();
        }
        let aws_lc_key = LessSafeKey::new(UnboundKey::new(alg, key).unwrap());
        let mut ossl = CipherCtx::new().unwrap();
        ossl.encrypt_init(Some(ossl_alg), Some(key), None).unwrap();
        let mut ossl_dec = CipherCtx::new().unwrap();
        ossl_dec
            .decrypt_init(Some(ossl_alg), Some(key), None)
            .unwrap();
        for &size in sizes {
            let data = Aligned::new(&vec![0u8; size], offsets.input);
            let mut out = Aligned::new(&vec![0u8; size + 1], offsets.output);
            let mut t = [0u8; 16];
            let mut ossl_out = Aligned::new(&vec![0u8; size + 1 + 16], offsets.output);
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

            let mut g = c.benchmark_group(format!("aes-{bits}-gcm-tls-seal") + label);
            g.throughput(Throughput::Bytes(size as u64 + 1));
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

            // Records shorter than 256 bytes, sealed in place too
            // (`encrypt_in_place`, as QUIC and aws-lc-rs's callers seal).
            if size < 256 {
                let mut g = c.benchmark_group(format!("aes-{bits}-gcm-tls-seal-in-place") + label);
                g.throughput(Throughput::Bytes(size as u64 + 1));
                g.bench_function(BenchmarkId::new(VG, size), |b| {
                    b.iter(|| {
                        vg_key
                            .encrypt_in_place(
                                black_box(&nonce),
                                black_box(&aad),
                                black_box(&mut record[..]),
                            )
                            .unwrap()
                    })
                });
                g.finish();
            }

            // Each iteration opens the record again from its ciphertext.
            let mut buf = Aligned::new(&ct, offsets.input);
            let mut g = c.benchmark_group(format!("aes-{bits}-gcm-tls-open") + label);
            g.throughput(Throughput::Bytes(size as u64 + 1));
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
}

/// A new connection: see `tls_records`.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn tls_connection_rows(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::aead::{AES_128_GCM, AES_256_GCM, Aad, LessSafeKey, Nonce, UnboundKey};
    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher::Cipher as OsslCipher;
    use openssl::cipher_ctx::CipherCtx;
    use verified_garbage::aes_gcm::AesGcm;

    use crate::{AWS_LC, OPENSSL, VG};

    let nonce = [0x24; 12];
    let aad = [0x17, 0x03, 0x03, 0x40, 0x11];
    let ty = [0x17u8];
    for (bits, key) in [(128, &[0x42u8; 16][..]), (256, &[0x42u8; 32][..])] {
        let (alg, ossl_alg) = if bits == 128 {
            (&AES_128_GCM, OsslCipher::aes_128_gcm())
        } else {
            (&AES_256_GCM, OsslCipher::aes_256_gcm())
        };
        // A new connection: its key set up, then `records` records of 255
        // bytes and their content type sealed with it. A connection of a
        // few records measures what the key's setup costs.
        let data = [0u8; 255];
        let mut out = [0u8; 256];
        let mut record = [0u8; 256];
        let mut ossl_out = [0u8; 256 + 16];
        let mut t = [0u8; 16];
        let mut g = c.benchmark_group(format!("aes-{bits}-gcm-tls-connection"));
        for records in [1, 2, 4, 16] {
            g.throughput(Throughput::Bytes((records * 256) as u64));
            g.bench_function(BenchmarkId::new(VG, records), |b| {
                b.iter(|| {
                    let k = AesGcm::new(black_box(key)).unwrap();
                    for _ in 0..records {
                        black_box(
                            k.encrypt(
                                black_box(&nonce),
                                black_box(&aad),
                                &[black_box(&data[..]), black_box(&ty[..])],
                                black_box(&mut out),
                            )
                            .unwrap(),
                        );
                    }
                })
            });
            g.bench_function(BenchmarkId::new(OPENSSL, records), |b| {
                b.iter(|| {
                    let mut ossl = CipherCtx::new().unwrap();
                    ossl.encrypt_init(Some(ossl_alg), Some(black_box(key)), None)
                        .unwrap();
                    for _ in 0..records {
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
                        black_box(t);
                    }
                })
            });
            g.bench_function(BenchmarkId::new(AWS_LC, records), |b| {
                b.iter(|| {
                    let k = LessSafeKey::new(UnboundKey::new(alg, black_box(key)).unwrap());
                    for _ in 0..records {
                        let _tag = black_box(
                            k.seal_in_place_separate_tag(
                                Nonce::assume_unique_for_key(*black_box(&nonce)),
                                Aad::from(black_box(&aad)),
                                black_box(&mut record),
                            )
                            .unwrap(),
                        );
                    }
                })
            });
        }
        g.finish();
    }
}

/// A key's setup and drop alone (`aes-*-gcm-new`, by the key's length in
/// bytes): what every benchmark that sets up a key for each message pays
/// besides the message, measured here rather than by subtracting a reused
/// key's time. OpenSSL sets up a context with the key, aws-lc-rs a
/// `LessSafeKey`.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn key_setup_rows(c: &mut Criterion) {
    use std::hint::black_box;

    use aws_lc_rs::aead::{AES_128_GCM, AES_256_GCM, LessSafeKey, UnboundKey};
    use criterion::BenchmarkId;
    use openssl::cipher::Cipher as OsslCipher;
    use openssl::cipher_ctx::CipherCtx;
    use verified_garbage::aes_gcm::AesGcm;

    use crate::{AWS_LC, OPENSSL, VG};

    for (bits, key) in [(128, &[0x42u8; 16][..]), (256, &[0x42u8; 32][..])] {
        let (alg, ossl_alg) = if bits == 128 {
            (&AES_128_GCM, OsslCipher::aes_128_gcm())
        } else {
            (&AES_256_GCM, OsslCipher::aes_256_gcm())
        };
        let mut g = c.benchmark_group(format!("aes-{bits}-gcm-new"));
        g.bench_function(BenchmarkId::new(VG, key.len()), |b| {
            b.iter(|| black_box(AesGcm::new(black_box(key)).unwrap()))
        });
        g.bench_function(BenchmarkId::new(OPENSSL, key.len()), |b| {
            b.iter(|| {
                let mut ossl = CipherCtx::new().unwrap();
                ossl.encrypt_init(Some(ossl_alg), Some(black_box(key)), None)
                    .unwrap();
                black_box(ossl)
            })
        });
        g.bench_function(BenchmarkId::new(AWS_LC, key.len()), |b| {
            b.iter(|| {
                black_box(LessSafeKey::new(
                    UnboundKey::new(alg, black_box(key)).unwrap(),
                ))
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
