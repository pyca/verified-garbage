//! AES-CBC, including key expansion and in-place encryption/decryption,
//! beside OpenSSL (aws-lc-rs has AES-CBC only with PKCS #7 padding).

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["aes_cbc", "aes"];

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

    use criterion::{BenchmarkId, Throughput};
    use openssl::cipher_ctx::CipherCtx;
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::aes_cbc::{AesCbcDecryptor, AesCbcEncryptor};

    use crate::{BenchDyn, OPENSSL, SIZES, VG};

    eprintln!("AES-CBC comparison: {}", openssl::version::version());
    let key: Vec<_> = (0..32).map(|i| (17 * i + 3) as u8).collect();
    let iv = [0x3c; 16];
    for (key_len, cipher) in [
        (16, Cipher::aes_128_cbc()),
        (24, Cipher::aes_192_cbc()),
        (32, Cipher::aes_256_cbc()),
    ] {
        let key = &key[..key_len];
        for (operation, encrypt, mode) in [
            ("encrypt", true, Mode::Encrypt),
            ("decrypt", false, Mode::Decrypt),
        ] {
            let mut group = c.benchmark_group(format!("aes-cbc-{operation}-{}", 8 * key_len));
            for size in SIZES.into_iter().chain([1024 * 1024]) {
                group.throughput(Throughput::Bytes(size as u64));
                let data = vec![0x5a; size];
                let mut buffer = crate::InPlace::new(size, &data);
                group.bench(BenchmarkId::new(VG, size), |b| {
                    b.iter(|| {
                        buffer.copy_from_slice(black_box(&data));
                        if encrypt {
                            let mut ctx =
                                AesCbcEncryptor::new(black_box(key), &black_box(iv)).unwrap();
                            ctx.encrypt(black_box(&mut buffer)).unwrap();
                        } else {
                            let mut ctx =
                                AesCbcDecryptor::new(black_box(key), &black_box(iv)).unwrap();
                            ctx.decrypt(black_box(&mut buffer)).unwrap();
                        }
                        black_box(&buffer);
                    })
                });
                let mut output = vec![0; size + 16];
                group.bench(BenchmarkId::new(OPENSSL, size), |b| {
                    b.iter(|| {
                        let mut ctx =
                            Crypter::new(cipher, mode, black_box(key), Some(black_box(&iv)))
                                .unwrap();
                        ctx.pad(false);
                        let n = ctx.update(black_box(&data), &mut output).unwrap();
                        let n = n + ctx.finalize(&mut output[n..]).unwrap();
                        black_box(&output[..n]);
                    })
                });
                // Match VG's in-place API, including the input copy. Keep the
                // original out-of-place EVP comparison above for continuity.
                let cipher_ref = openssl::cipher::Cipher::from_nid(cipher.nid()).unwrap();
                group.bench(BenchmarkId::new("openssl-inplace", size), |b| {
                    b.iter(|| {
                        let mut ctx = CipherCtx::new().unwrap();
                        if encrypt {
                            ctx.encrypt_init(
                                Some(cipher_ref),
                                Some(black_box(key)),
                                Some(black_box(&iv)),
                            )
                            .unwrap();
                        } else {
                            ctx.decrypt_init(
                                Some(cipher_ref),
                                Some(black_box(key)),
                                Some(black_box(&iv)),
                            )
                            .unwrap();
                        }
                        ctx.set_padding(false);
                        output[..size].copy_from_slice(black_box(&data));
                        let n = ctx
                            .cipher_update_inplace(black_box(&mut output), size)
                            .unwrap();
                        let n = n + ctx.cipher_final(&mut output[n..]).unwrap();
                        black_box(&output[..n]);
                    })
                });
            }
            group.finish();
        }
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
