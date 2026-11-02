//! X448 (aws-lc-rs has no X448, so OpenSSL is its only comparison).

use criterion::Criterion;

pub const USES: &[&str] = &["x448"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    use std::hint::black_box;
    #[cfg(target_arch = "riscv64")]
    {
        let x: [u64; 8] = core::array::from_fn(|i| 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i as u64 + 1));
        let mut g = c.benchmark_group("c910_probe");
        g.bench_function(criterion::BenchmarkId::new(crate::VG, "k64"), |b| b.iter(|| probe::k64(black_box(1000), black_box(&x))));
        g.bench_function(criterion::BenchmarkId::new(crate::VG, "k56"), |b| b.iter(|| probe::k56(black_box(1000), black_box(&x))));
        g.bench_function(criterion::BenchmarkId::new(crate::VG, "klo"), |b| b.iter(|| probe::klo(black_box(1000), black_box(&x))));
        g.bench_function(criterion::BenchmarkId::new(crate::VG, "kalu"), |b| b.iter(|| probe::kalu(black_box(1000), black_box(&x))));
        g.finish();
    }

    use criterion::BenchmarkId;
    use openssl::derive::Deriver;
    use openssl::pkey::{Id, PKey};
    use verified_garbage::x448::{PrivateKey, x448};

    use crate::{OPENSSL, VG, fixed_tape};
    let private = [0x42; 56];
    let peer = PrivateKey::from_bytes(&[0x24; 56]).public_key();
    // Each side's private key is loaded once, outside the measurements, as a
    // party holds its key across exchanges (OpenSSL's import also derives
    // the public key, a second scalar multiplication); the peer's public key
    // comes with each exchange.
    let vg_private = PrivateKey::from_bytes(&private);
    let openssl_private = PKey::private_key_from_raw_bytes(&private, Id::X448).unwrap();
    let mut g = c.benchmark_group("x448");
    // One Diffie-Hellman: a shared secret from a private key and the peer's
    // public key. The ids' size is the bytes of the shared secret.
    g.bench_function(BenchmarkId::new(VG, 56), |b| {
        b.iter(|| {
            black_box(&vg_private)
                .diffie_hellman(black_box(&peer))
                .unwrap()
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 56), |b| {
        b.iter(|| {
            let peer = PKey::public_key_from_raw_bytes(black_box(&peer), Id::X448).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.finish();

    // OpenSSL has no function of the scalar multiplication alone: its nearest
    // is the same Diffie-Hellman (which also rejects an all-zero secret).
    let mut g = c.benchmark_group("x448_raw");
    g.bench_function(BenchmarkId::new(VG, 56), |b| {
        b.iter(|| x448(black_box(&private), black_box(&peer)))
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 56), |b| {
        b.iter(|| {
            let peer = PKey::public_key_from_raw_bytes(black_box(&peer), Id::X448).unwrap();
            let mut d = Deriver::new(black_box(&openssl_private)).unwrap();
            d.set_peer(&peer).unwrap();
            d.derive_to_vec().unwrap()
        })
    });
    g.finish();

    let mut g = c.benchmark_group("x448_public_key");
    g.bench_function(BenchmarkId::new(VG, 56), |b| {
        b.iter(|| PrivateKey::from_bytes(black_box(&private)).public_key())
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 56), |b| {
        b.iter(|| {
            PKey::private_key_from_raw_bytes(black_box(&private), Id::X448)
                .unwrap()
                .raw_public_key()
                .unwrap()
        })
    });
    g.finish();

    // A new key pair: a private key and its public key, which OpenSSL's key
    // generation always derives. verified-garbage's private key is from a
    // fixed tape (`PrivateKey::generate` but for `getrandom`); OpenSSL draws
    // from its own generator.
    let mut g = c.benchmark_group("x448_generate");
    g.bench_function(BenchmarkId::new(VG, 56), |b| {
        b.iter(|| {
            let mut bytes = [0; 56];
            fixed_tape(56)(&mut bytes);
            let key = PrivateKey::from_bytes(&bytes);
            (*key.as_bytes(), key.public_key())
        })
    });
    g.bench_function(BenchmarkId::new(OPENSSL, 56), |b| {
        b.iter(|| {
            let key = PKey::generate_x448().unwrap();
            (
                key.raw_private_key().unwrap(),
                key.raw_public_key().unwrap(),
            )
        })
    });
    g.finish();
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}

// THROWAWAY PROBE (never merged): the C910 multiplier's throughput, to choose
// between radix 2^64 (mul + mulhu + 6 ALU per product) and radix 2^56
// (mul + mulhu + 4 ALU per product) for X448's field.
#[cfg(target_arch = "riscv64")]
mod probe {
/// Throughput kernels: `n` iterations of 8 products each, accumulated the
/// way each radix does. Operands vary each iteration (one add each).
#[inline(never)]
pub fn k64(n: u64, x: &[u64; 8]) -> u64 {
    let mut a = *x;
    let (mut l0, mut h0, mut t0) = (0u64, 0u64, 0u64);
    let (mut l1, mut h1, mut t1) = (0u64, 0u64, 0u64);
    for _ in 0..n {
        for i in 0..4 {
            let p = (a[i] as u128) * (a[i + 4] as u128);
            let (lo, hi) = (p as u64, (p >> 64) as u64);
            let (s, c) = l0.overflowing_add(lo);
            l0 = s;
            let (s, c2) = h0.overflowing_add(hi + c as u64);
            h0 = s;
            t0 += c2 as u64;
            let p = (a[i + 4] as u128) * (a[(i + 1) % 4] as u128);
            let (lo, hi) = (p as u64, (p >> 64) as u64);
            let (s, c) = l1.overflowing_add(lo);
            l1 = s;
            let (s, c2) = h1.overflowing_add(hi + c as u64);
            h1 = s;
            t1 += c2 as u64;
        }
        for j in 0..8 {
            a[j] = a[j].wrapping_add(if j < 4 { l0 } else { l1 });
        }
    }
    l0 ^ h0 ^ t0 ^ l1 ^ h1 ^ t1
}

#[inline(never)]
pub fn k56(n: u64, x: &[u64; 8]) -> u64 {
    let mut a = *x;
    let (mut c0, mut c1) = (0u128, 0u128);
    for _ in 0..n {
        for i in 0..4 {
            c0 += (a[i] as u128) * (a[i + 4] as u128);
            c1 += (a[i + 4] as u128) * (a[(i + 1) % 4] as u128);
        }
        for j in 0..8 {
            a[j] = a[j].wrapping_add(if j < 4 { c0 as u64 } else { c1 as u64 });
        }
    }
    (c0 ^ c1) as u64 ^ ((c0 ^ c1) >> 64) as u64
}

/// Only `mul` (the low half), as many as `k64`'s pairs.
#[inline(never)]
pub fn klo(n: u64, x: &[u64; 8]) -> u64 {
    let mut a = *x;
    let (mut c0, mut c1) = (0u64, 0u64);
    for _ in 0..n {
        for i in 0..4 {
            c0 = c0.wrapping_add(a[i].wrapping_mul(a[i + 4]));
            c1 = c1.wrapping_add(a[i + 4].wrapping_mul(a[(i + 1) % 4]));
        }
        for j in 0..8 {
            a[j] = a[j].wrapping_add(if j < 4 { c0 } else { c1 });
        }
    }
    c0 ^ c1
}

/// ALU only, for calibration: 24 dependent-in-pairs adds/xors/ors.
#[inline(never)]
pub fn kalu(n: u64, x: &[u64; 8]) -> u64 {
    let mut a = *x;
    let (mut c0, mut c1) = (0u64, 0u64);
    for _ in 0..n {
        for i in 0..4 {
            c0 = c0.wrapping_add(a[i] ^ a[i + 4]);
            c1 = c1.wrapping_add(a[i + 4] | a[(i + 1) % 4]);
            c0 ^= c1;
        }
        for j in 0..8 {
            a[j] = a[j].wrapping_add(if j < 4 { c0 } else { c1 });
        }
    }
    c0 ^ c1
}

}
