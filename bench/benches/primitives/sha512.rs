//! SHA-512.

use std::hint::black_box;

use criterion::{BenchmarkId, Criterion};
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hashes::sha512::Sha512;
use verified_garbage::hashes::sha512_224::Sha512_224;
use verified_garbage::hashes::sha512_256::Sha512_256;

use crate::hash_group;

pub const USES: &[&str] = &["sha512"];

pub fn bench(c: &mut Criterion) {
    hash_group(
        c,
        "sha512",
        Sha512::digest,
        MessageDigest::sha512(),
        Some(&aws_lc_rs::digest::SHA512),
    );
    probe(c);
}

// EXPERIMENT (not for merge): where the 64-byte digests' time depends on
// the addresses involved.

#[inline(never)]
fn deep<R>(n: usize, f: &dyn Fn() -> R) -> R {
    let pad = black_box([0u8; 64]);
    if n == 0 {
        let r = f();
        black_box(&pad);
        r
    } else {
        let r = deep(n - 1, f);
        black_box(&pad);
        r
    }
}

#[inline(never)]
fn stack_addr(n: usize) -> usize {
    deep(n, &|| {
        let x = black_box(0u8);
        &x as *const u8 as usize
    })
}

fn probe(c: &mut Criterion) {
    let mut g = c.benchmark_group("sha512probe");
    let buf = vec![0x5au8; 3 * 4096];
    let start = (4096 - buf.as_ptr() as usize % 4096) % 4096;
    eprintln!("probe: buf mod 4096 = {}", buf.as_ptr() as usize % 4096);
    for off in (0..4096).step_by(256) {
        let d = &buf[start + off..start + off + 64];
        g.bench_function(BenchmarkId::new("verified-garbage", off), |b| {
            b.iter(|| Sha512::digest(black_box(d)))
        });
    }
    let d = &buf[start..start + 64];
    for n in 0..8 {
        eprintln!("probe: depth {n} local mod 4096 = {}", stack_addr(n) % 4096);
        g.bench_function(BenchmarkId::new("verified-garbage", 10000 + n), |b| {
            b.iter(|| deep(n, &|| Sha512::digest(black_box(d))))
        });
    }
    g.bench_function(BenchmarkId::new("verified-garbage", 20384), |b| b.iter(|| Sha384::digest(black_box(d))));
    g.bench_function(BenchmarkId::new("verified-garbage", 20512), |b| b.iter(|| Sha512::digest(black_box(d))));
    g.bench_function(BenchmarkId::new("verified-garbage", 20224), |b| b.iter(|| Sha512_224::digest(black_box(d))));
    g.bench_function(BenchmarkId::new("verified-garbage", 20256), |b| b.iter(|| Sha512_256::digest(black_box(d))));
    g.finish();
}
