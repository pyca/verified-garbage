//! AES-CCM.

use criterion::Criterion;

pub const USES: &[&str] = &["aes_ccm", "aes", "cmac_aes"];

/// One-shot AES-CCM encryption and decryption (key setup included), with
/// a 12-byte nonce, 16 bytes of associated data and a 16-byte tag, as
/// OpenSSL's CCM implementation does it (its lengths set first, as CCM needs).
#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;

    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher::Cipher;
    use openssl::cipher_ctx::CipherCtx;
    use verified_garbage::aead::aes_ccm::AesCcm;

    use crate::{BenchDyn, OPENSSL, VG};
    const SIZES: [usize; 12] = [0, 1, 7, 15, 16, 17, 31, 32, 63, 64, 1024, 16384];

    for key_len in [16, 24, 32] {
        let key = vec![0x42; key_len];
        let nonce = [0x24; 12];
        let aad = [0x5a; 16];
        let cipher = match key_len {
            16 => Cipher::aes_128_ccm(),
            24 => Cipher::aes_192_ccm(),
            _ => Cipher::aes_256_ccm(),
        };
        for size in SIZES {
            let data = vec![0u8; size];
            let mut buf = data.clone();
            let tag = AesCcm::new(&key)
                .unwrap()
                .encrypt_in_place::<16>(&nonce, &aad, &mut buf)
                .unwrap();
            let ct = buf.clone();
            let mut out = vec![0u8; size];

            let mut g = c.benchmark_group(format!("aes-{}-ccm-encrypt", key_len * 8));
            g.throughput(Throughput::Bytes(size as u64));
            g.bench(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    let k = AesCcm::new(black_box(&key)).unwrap();
                    k.encrypt_in_place::<16>(
                        black_box(&nonce),
                        black_box(&aad),
                        black_box(&mut buf),
                    )
                    .unwrap()
                })
            });
            let mut t = [0u8; 16];
            g.bench(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx = CipherCtx::new().unwrap();
                    ctx.encrypt_init(Some(cipher), None, None).unwrap();
                    ctx.set_iv_length(12).unwrap();
                    ctx.set_tag_length(16).unwrap();
                    ctx.encrypt_init(None, Some(black_box(&key)), Some(black_box(&nonce)))
                        .unwrap();
                    ctx.set_data_len(size).unwrap();
                    ctx.cipher_update(black_box(&aad), None).unwrap();
                    ctx.cipher_update(black_box(&data), Some(&mut out)).unwrap();
                    ctx.cipher_final(&mut []).unwrap();
                    ctx.tag(&mut t).unwrap();
                })
            });
            g.finish();

            let mut g = c.benchmark_group(format!("aes-{}-ccm-decrypt", key_len * 8));
            g.throughput(Throughput::Bytes(size as u64));
            g.bench(BenchmarkId::new(VG, size), |b| {
                b.iter(|| {
                    buf.copy_from_slice(&ct);
                    let k = AesCcm::new(black_box(&key)).unwrap();
                    k.decrypt_in_place(
                        black_box(&nonce),
                        black_box(&aad),
                        black_box(&mut buf),
                        &tag,
                    )
                    .unwrap()
                })
            });
            g.bench(BenchmarkId::new(OPENSSL, size), |b| {
                b.iter(|| {
                    let mut ctx = CipherCtx::new().unwrap();
                    ctx.decrypt_init(Some(cipher), None, None).unwrap();
                    ctx.set_iv_length(12).unwrap();
                    ctx.set_tag(&tag).unwrap();
                    ctx.decrypt_init(None, Some(black_box(&key)), Some(black_box(&nonce)))
                        .unwrap();
                    ctx.set_data_len(size).unwrap();
                    ctx.cipher_update(black_box(&aad), None).unwrap();
                    ctx.cipher_update(black_box(&ct), Some(&mut out)).unwrap();
                })
            });
            g.finish();
        }
    }
}

#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
