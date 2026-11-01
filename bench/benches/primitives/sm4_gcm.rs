//! SM4-GCM: one-shot encryption and decryption (key setup included), and
//! streaming encryption, with a 12-byte nonce and 16 bytes of additional
//! data, as RFC 8998's TLS cipher suite uses it.
//!
//! aws-lc-rs has no SM4. OpenSSL has SM4-GCM from 3.2 on; with an older
//! OpenSSL there is nothing of its to compare with.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["sm4_gcm", "sm4", "gcm"];

#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher::Cipher;
    use openssl::cipher_ctx::CipherCtx;
    use verified_garbage::sm4_gcm::Sm4Gcm;

    use crate::{OPENSSL, SIZES, VG};

    let key: [u8; 16] = core::array::from_fn(|i| (17 * i + 3) as u8);
    let nonce: [u8; 12] = core::array::from_fn(|i| (5 * i + 1) as u8);
    let aad = [0x5a; 16];
    let cipher = Cipher::fetch(None, "SM4-GCM", None).ok();
    for size in SIZES {
        let data = vec![0x42u8; size];
        let mut ct = data.clone();
        let tag = Sm4Gcm::new(&key)
            .encrypt_in_place(&nonce, &aad, &mut ct)
            .unwrap();
        // OpenSSL's encryption, from which it is measured.
        let openssl_encrypt =
            |cipher: &openssl::cipher::CipherRef, out: &mut [u8], t: &mut [u8]| {
                let mut ctx = CipherCtx::new().unwrap();
                ctx.encrypt_init(Some(cipher), Some(black_box(&key)), Some(black_box(&nonce)))
                    .unwrap();
                ctx.cipher_update(black_box(&aad), None).unwrap();
                let n = ctx.cipher_update(black_box(&data), Some(out)).unwrap();
                ctx.cipher_final(&mut out[n..]).unwrap();
                ctx.tag(t).unwrap();
            };
        let mut out = vec![0u8; size + 16];
        if let Some(cipher) = &cipher {
            let mut t = [0u8; 16];
            openssl_encrypt(cipher, &mut out, &mut t);
            assert_eq!((&out[..size], t), (&ct[..], tag));
        }

        let mut g = c.benchmark_group("sm4-gcm-encrypt");
        g.throughput(Throughput::Bytes(size as u64));
        let mut buf = data.clone();
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                Sm4Gcm::new(black_box(&key))
                    .encrypt_in_place(black_box(&nonce), black_box(&aad), black_box(&mut buf))
                    .unwrap()
            })
        });
        if let Some(cipher) = &cipher {
            let mut t = [0u8; 16];
            g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| openssl_encrypt(cipher, &mut out, &mut t))
            });
        }
        g.finish();

        let mut g = c.benchmark_group("sm4-gcm-decrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                buf.copy_from_slice(&ct);
                Sm4Gcm::new(black_box(&key))
                    .decrypt_in_place(
                        black_box(&nonce),
                        black_box(&aad),
                        black_box(&mut buf),
                        black_box(&tag),
                    )
                    .unwrap()
            })
        });
        if let Some(cipher) = &cipher {
            g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx = CipherCtx::new().unwrap();
                    ctx.decrypt_init(Some(cipher), Some(black_box(&key)), Some(black_box(&nonce)))
                        .unwrap();
                    ctx.set_tag(black_box(&tag)).unwrap();
                    ctx.cipher_update(black_box(&aad), None).unwrap();
                    let n = ctx.cipher_update(black_box(&ct), Some(&mut out)).unwrap();
                    ctx.cipher_final(&mut out[n..]).unwrap();
                })
            });
        }
        g.finish();

        // Streaming, a key reused: the plaintext in two halves.
        let k = Sm4Gcm::new(&key);
        let mut g = c.benchmark_group("sm4-gcm-stream-encrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut s = k.encryptor(black_box(&nonce)).unwrap();
                s.update_aad(black_box(&aad)).unwrap();
                let (x, y) = buf.split_at_mut(size / 2);
                s.update(black_box(x)).unwrap();
                s.update(black_box(y)).unwrap();
                s.finalize()
            })
        });
        g.finish();
    }
}

#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
