//! ChaCha20.
//!
//! aws-lc-rs exposes ChaCha20 only inside its AEADs and QUIC header
//! protection (one 5-byte mask), not as a stream cipher, so there is nothing
//! of its to compare with.

use criterion::Criterion;

/// The shared sizes, and TLS 1.3's records of 1 KiB and 4 KiB of payload,
/// whose plaintext is one byte longer (the content type): a partial last
/// block, which ChaCha20-Poly1305 encrypts at these sizes too; 480 bytes;
/// and short inputs: QUIC's header protection mask (5 bytes, RFC 9001 §5.4.4), part
/// of one block (16 bytes) and two blocks (128 bytes).
const SIZES: [usize; 9] = [5, 16, 64, 128, 480, 1024, 1025, 4097, 16384];

pub const USES: &[&str] = &["chacha20"];

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}

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
    use openssl::symm::{Cipher, Crypter, Mode};
    use verified_garbage::chacha20::ChaCha20;

    use crate::{OPENSSL, VG};

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
    }
    g.finish();
}
