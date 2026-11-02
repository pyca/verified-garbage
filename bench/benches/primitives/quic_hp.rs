//! QUIC header protection (RFC 9001 §5.4): the 5-byte mask of a 16-byte
//! sample, as rustls computes it for every packet. The header protection key
//! lives as long as the packet keys, so it is made once, outside the loop:
//! for AES the mask is one ECB block of the sample under the expanded key;
//! for ChaCha20 the sample is the counter and nonce of a fresh ChaCha20,
//! whose first five bytes of keystream are the mask. aws-lc-rs computes the
//! same with `aead::quic::HeaderProtectionKey::new_mask`.

use criterion::Criterion;

/// The library modules whose code these benchmarks run.
pub const USES: &[&str] = &["aes_ecb", "aes", "chacha20"];

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

    use aws_lc_rs::aead::quic::{AES_128, AES_256, CHACHA20, HeaderProtectionKey};
    use criterion::{BenchmarkId, Throughput};
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::aes_ecb::AesEcb;
    use verified_garbage::chacha20::ChaCha20;

    use crate::{AWS_LC, BenchDyn, OPENSSL, VG};

    const SAMPLE: usize = 16;
    let key: Vec<_> = (0..32).map(|i| (17 * i + 3) as u8).collect();
    let sample = [0x5a; SAMPLE];

    for (key_len, cipher, algorithm) in [
        (16, Cipher::aes_128_ecb(), &AES_128),
        (32, Cipher::aes_256_ecb(), &AES_256),
    ] {
        let key = &key[..key_len];
        let mut group = c.benchmark_group(format!("quic-hp-aes-{}", 8 * key_len));
        group.throughput(Throughput::Bytes(SAMPLE as u64));
        let vg = AesEcb::new(key).unwrap();
        group.bench(BenchmarkId::new(VG, SAMPLE), |b| {
            b.iter(|| {
                let mut block = *black_box(&sample);
                vg.encrypt(&mut block).unwrap();
                let mut mask = [0u8; 5];
                mask.copy_from_slice(&block[..5]);
                black_box(mask)
            })
        });
        let mut ossl = Crypter::new(cipher, Mode::Encrypt, key, None).unwrap();
        ossl.pad(false);
        let mut out = [0u8; 2 * SAMPLE];
        group.bench(BenchmarkId::new(OPENSSL, SAMPLE), |b| {
            b.iter(|| {
                ossl.update(black_box(&sample), &mut out).unwrap();
                let mut mask = [0u8; 5];
                mask.copy_from_slice(&out[..5]);
                black_box(mask)
            })
        });
        let aws = HeaderProtectionKey::new(algorithm, key).unwrap();
        group.bench(BenchmarkId::new(AWS_LC, SAMPLE), |b| {
            b.iter(|| black_box(aws.new_mask(black_box(&sample)).unwrap()))
        });
        group.finish();
    }

    let key: [u8; 32] = key.try_into().unwrap();
    let mut group = c.benchmark_group("quic-hp-chacha20");
    group.throughput(Throughput::Bytes(SAMPLE as u64));
    group.bench(BenchmarkId::new(VG, SAMPLE), |b| {
        b.iter(|| {
            let mut mask = [0u8; 5];
            ChaCha20::new(&key, black_box(&sample)).apply_keystream(&mut mask);
            black_box(mask)
        })
    });
    // OpenSSL's ChaCha20 takes the sample as its 16-byte IV (counter ‖
    // nonce), as RFC 9001 §5.4.4 does.
    let mut out = [0u8; 5 + 64];
    group.bench(BenchmarkId::new(OPENSSL, SAMPLE), |b| {
        b.iter(|| {
            let mut c = Crypter::new(
                Cipher::chacha20(),
                Mode::Encrypt,
                &key,
                Some(black_box(&sample)),
            )
            .unwrap();
            c.update(&[0u8; 5], &mut out).unwrap();
            let mut mask = [0u8; 5];
            mask.copy_from_slice(&out[..5]);
            black_box(mask)
        })
    });
    let aws = HeaderProtectionKey::new(&CHACHA20, &key).unwrap();
    group.bench(BenchmarkId::new(AWS_LC, SAMPLE), |b| {
        b.iter(|| black_box(aws.new_mask(black_box(&sample)).unwrap()))
    });
    group.finish();
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
