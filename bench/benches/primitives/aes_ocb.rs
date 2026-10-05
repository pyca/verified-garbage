//! AES-OCB.

use criterion::Criterion;

pub const USES: &[&str] = &["aes_ocb", "aes"];

/// One-shot AES-128-OCB encryption and decryption (key setup included), with
/// a 12-byte nonce, 16 bytes of associated data and a 16-byte tag, as
/// OpenSSL's `EVP_aes_128_ocb` does it.
#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher::Cipher;
    use openssl::cipher_ctx::CipherCtx;
    use verified_garbage::aes_ocb::AesOcb;

    use crate::{OPENSSL, SIZES, VG};

    let key = [0x42; 16];
    let nonce = [0x24; 12];
    let aad = [0x5a; 16];
    let cipher = Cipher::aes_128_ocb();
    for size in SIZES {
        let data = vec![0u8; size];
        let mut buf = data.clone();
        let tag = AesOcb::new(&key)
            .unwrap()
            .encrypt_in_place::<16>(&nonce, &aad, &mut buf)
            .unwrap();
        let ct = buf.clone();
        let mut out = vec![0u8; size + 16];

        let mut g = c.benchmark_group("aes-128-ocb-encrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let k = AesOcb::new(black_box(&key)).unwrap();
                k.encrypt_in_place::<16>(black_box(&nonce), black_box(&aad), black_box(&mut buf))
                    .unwrap()
            })
        });
        let mut t = [0u8; 16];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut ctx = CipherCtx::new().unwrap();
                ctx.encrypt_init(Some(cipher), None, None).unwrap();
                ctx.set_iv_length(12).unwrap();
                ctx.set_tag_length(16).unwrap();
                ctx.encrypt_init(None, Some(black_box(&key)), Some(black_box(&nonce)))
                    .unwrap();
                ctx.cipher_update(black_box(&aad), None).unwrap();
                let n = ctx.cipher_update(black_box(&data), Some(&mut out)).unwrap();
                ctx.cipher_final(&mut out[n..]).unwrap();
                ctx.tag(&mut t).unwrap();
            })
        });
        g.finish();

        let mut g = c.benchmark_group("aes-128-ocb-decrypt");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                buf.copy_from_slice(&ct);
                let k = AesOcb::new(black_box(&key)).unwrap();
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
                let mut ctx = CipherCtx::new().unwrap();
                ctx.decrypt_init(Some(cipher), None, None).unwrap();
                ctx.set_iv_length(12).unwrap();
                ctx.set_tag(&tag).unwrap();
                ctx.decrypt_init(None, Some(black_box(&key)), Some(black_box(&nonce)))
                    .unwrap();
                ctx.cipher_update(black_box(&aad), None).unwrap();
                let n = ctx.cipher_update(black_box(&ct), Some(&mut out)).unwrap();
                ctx.cipher_final(&mut out[n..]).unwrap();
            })
        });
        g.finish();
    }
}

#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm"
)))]
pub fn bench(_: &mut Criterion) {}
