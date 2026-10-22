//! ChaCha20.
//!
//! aws-lc-rs exposes ChaCha20 only inside its AEADs and QUIC header
//! protection (one 5-byte mask), not as a stream cipher, so there is nothing
//! of its to compare with.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput};
use openssl::symm::{Cipher, Crypter, Mode};
use verified_garbage::chacha20::ChaCha20;

use crate::{OPENSSL, VG};

/// The shared sizes, and TLS 1.3's records of 1 KiB and 4 KiB of payload,
/// whose plaintext is one byte longer (the content type): a partial last
/// block, which ChaCha20-Poly1305 encrypts at these sizes too; and 480
/// bytes, which leave 224 after the AArch64 code's whole 256-byte chunks.
const SIZES: [usize; 11] = [64, 128, 192, 256, 320, 384, 448, 480, 1024, 1025, 4097];

pub const USES: &[&str] = &["chacha20"];

pub fn bench(c: &mut Criterion) {
    let key = [0x42; 32];
    let nonce = [0x24; 16];
    let mut g = c.benchmark_group("chacha20");
    for size in SIZES {
        g.throughput(Throughput::Bytes(size as u64));
        let mut data = vec![0u8; size];
        g.bench_function(BenchmarkId::new(VG, size), |b| {
            b.iter(|| {
                let mut c = ChaCha20::new(black_box(&key), black_box(&nonce));
                c.apply_keystream(black_box(&mut data));
            })
        });
        // OpenSSL's ChaCha20 takes the same 16-byte nonce (counter ‖ nonce).
        let mut out = vec![0u8; size + Cipher::chacha20().block_size()];
        g.bench_function(BenchmarkId::new(OPENSSL, size), |b| {
            b.iter(|| {
                let mut c = Crypter::new(
                    Cipher::chacha20(),
                    Mode::Encrypt,
                    black_box(&key),
                    Some(black_box(&nonce)),
                )
                .unwrap();
                c.update(black_box(&data), &mut out).unwrap();
            })
        });
        // Diagnostic: AWS-LC's own ChaCha20 (`ChaCha20_ctr32_avx2` on x86-64).
        #[cfg(target_arch = "x86_64")]
        {
            let mut out = vec![0u8; size];
            g.bench_function(BenchmarkId::new(crate::AWS_LC, size), |b| {
                b.iter(|| unsafe {
                    aws_lc_sys::CRYPTO_chacha_20(
                        out.as_mut_ptr(),
                        black_box(data.as_ptr()),
                        size,
                        black_box(key.as_ptr()),
                        black_box(nonce[4..].as_ptr()),
                        0,
                    )
                })
            });
        }
    }
    g.finish();
}
