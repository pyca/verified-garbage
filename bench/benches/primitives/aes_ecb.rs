//! AES-ECB, including key expansion and in-place encryption/decryption.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["aes_ecb", "aes"];

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

    use aws_lc_rs::cipher::{
        AES_128, AES_192, AES_256, DecryptingKey, DecryptionContext, EncryptingKey,
        UnboundCipherKey,
    };
    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::cipher::aes::AesEcb;

    use crate::{AWS_LC, BenchDyn, OPENSSL, VG};

    let key: Vec<_> = (0..32).map(|i| (17 * i + 3) as u8).collect();
    for (key_len, cipher, algorithm) in [
        (16, Cipher::aes_128_ecb(), &AES_128),
        (24, Cipher::aes_192_ecb(), &AES_192),
        (32, Cipher::aes_256_ecb(), &AES_256),
    ] {
        let key = &key[..key_len];
        for (operation, encrypt, mode) in [
            ("encrypt", true, Mode::Encrypt),
            ("decrypt", false, Mode::Decrypt),
        ] {
            let mut group = c.benchmark_group(format!("aes-ecb-{operation}-{}", 8 * key_len));
            for size in [16usize, 32, 240, 1024, 16384] {
                group.throughput(Throughput::Bytes(size as u64));
                let data = vec![0x5a; size];
                let mut buffer = crate::InPlace::new(size, &data);
                let ctx = AesEcb::new(key).unwrap();
                let mut check = data.clone();
                if encrypt {ctx.encrypt(&mut check).unwrap();} else {ctx.decrypt(&mut check).unwrap();}
                let mut expected = vec![0; size+16];
                let mut reference = Crypter::new(cipher,mode,key,None).unwrap();
                reference.pad(false);
                let written=reference.update(&data,&mut expected).unwrap();
                let final_len=reference.finalize(&mut expected[written..]).unwrap();
                assert_eq!(size,written+final_len);
                assert_eq!(&check[..],&expected[..size]);
                group.bench(BenchmarkId::new(VG, size), |b| {
                    b.iter(|| {
                        if encrypt {ctx.encrypt(black_box(&mut buffer)).unwrap();} else {ctx.decrypt(black_box(&mut buffer)).unwrap();}
                        black_box(&buffer);
                    })
                });
                let mut output = vec![0; size + 16];
                group.bench(BenchmarkId::new(OPENSSL, size), |b| {
                    b.iter(|| {
                        let mut ctx = Crypter::new(cipher, mode, black_box(key), None).unwrap();
                        ctx.pad(false);
                        let n = ctx.update(black_box(&data), &mut output).unwrap();
                        let n = n + ctx.finalize(&mut output[n..]).unwrap();
                        black_box(&output[..n]);
                    })
                });
                group.bench(BenchmarkId::new(AWS_LC, size), |b| {
                    b.iter(|| {
                        let unbound = UnboundCipherKey::new(algorithm, black_box(key)).unwrap();
                        buffer.copy_from_slice(black_box(&data));
                        if encrypt {
                            let ctx = EncryptingKey::ecb(unbound).unwrap();
                            ctx.encrypt(black_box(&mut buffer)).unwrap();
                        } else {
                            let ctx = DecryptingKey::ecb(unbound).unwrap();
                            ctx.decrypt(black_box(&mut buffer), DecryptionContext::None)
                                .unwrap();
                        }
                        black_box(&buffer);
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
