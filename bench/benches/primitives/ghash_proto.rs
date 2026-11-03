//! Bench-only: a prototype GHASH by integer multiplication with holes,
//! next to `vg_ghash` (through AES-GCM with additional data only). Not for merging.

use criterion::Criterion;

pub const USES: &[&str] = &["gcm"];

#[cfg(target_arch = "riscv64")]
pub fn bench(c: &mut Criterion) {
    use criterion::{BenchmarkId, Throughput};
    use std::hint::black_box;
    use verified_garbage::aes_gcm::AesGcm;
    let key = [0x42u8; 16];
    let k = AesGcm::new(&key).unwrap();
    let h = [0x66u8, 0xe9, 0x4b, 0xd4, 0xef, 0x8a, 0x2c, 0x3b, 0x88, 0x4c, 0xfa, 0x59, 0xca, 0x34, 0x2b, 0x2e];
    for size in [1024usize, 8192] {
        let aad = vec![0x5au8; size];
        let mut g = c.benchmark_group("ghash-table");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new("verified-garbage", size), |b| {
            b.iter(|| k.encrypt_in_place(black_box(&[0u8; 12]), black_box(&aad), &mut []).unwrap())
        });
        g.finish();
        let mut g = c.benchmark_group("ghash-mul");
        g.throughput(Throughput::Bytes(size as u64));
        g.bench_function(BenchmarkId::new("verified-garbage", size), |b| {
            b.iter(|| {
                let mut y = [0u8; 16];
                proto2::ghash(black_box(&h), &mut y, black_box(&aad));
                y
            })
        });
        g.finish();
    }
}

#[cfg(not(target_arch = "riscv64"))]
pub fn bench(_: &mut Criterion) {}

#[allow(dead_code)]
pub mod proto {
    const M32: [u64; 4] = [0x11111111, 0x22222222, 0x44444444, 0x88888888];
    const M64: [u64; 4] = [0x1111111111111111, 0x2222222222222222, 0x4444444444444444, 0x8888888888888888];
    /// Carry-less product of two 32-bit values (as u64), by integer multiplication with holes.
    #[inline(always)]
    pub fn cl32(a: u64, b: [u64; 4]) -> u64 {
        let a0 = a & M32[0]; let a1 = a & M32[1]; let a2 = a & M32[2]; let a3 = a & M32[3];
        let z0 = (a0 * b[0]) ^ (a1 * b[3]) ^ (a2 * b[2]) ^ (a3 * b[1]);
        let z1 = (a0 * b[1]) ^ (a1 * b[0]) ^ (a2 * b[3]) ^ (a3 * b[2]);
        let z2 = (a0 * b[2]) ^ (a1 * b[1]) ^ (a2 * b[0]) ^ (a3 * b[3]);
        let z3 = (a0 * b[3]) ^ (a1 * b[2]) ^ (a2 * b[1]) ^ (a3 * b[0]);
        (z0 & M64[0]) | (z1 & M64[1]) | (z2 & M64[2]) | (z3 & M64[3])
    }
    pub fn split(b: u64) -> [u64; 4] { [b & M32[0], b & M32[1], b & M32[2], b & M32[3]] }
    /// The 9 split 32-bit operands of H: Karatsuba at both levels.
    pub fn prep(h: [u64; 2]) -> [[u64; 4]; 9] {
        let (hh, hl) = (h[0], h[1]); let hm = hh ^ hl;
        let p = |x: u64| { let (x1, x0) = (x >> 32, x & 0xffffffff); [split(x0), split(x1), split(x0 ^ x1)] };
        let [a, b, c] = p(hl); let [d, e, f] = p(hh); let [g, i, j] = p(hm);
        [a, b, c, d, e, f, g, i, j]
    }
    #[inline(always)]
    fn cl64(x: u64, t: &[[u64; 4]]) -> (u64, u64) {
        let (x1, x0) = (x >> 32, x & 0xffffffff);
        let lo = cl32(x0, t[0]); let hi = cl32(x1, t[1]); let mid = cl32(x0 ^ x1, t[2]) ^ lo ^ hi;
        (hi ^ (mid >> 32), lo ^ (mid << 32))
    }
    /// Y = Y • H, Y and H as two big-endian words (most significant first).
    pub fn mul(y: [u64; 2], t: &[[u64; 4]; 9]) -> [u64; 2] {
        let (yh, yl) = (y[0], y[1]);
        let (l1, l0) = cl64(yl, &t[0..3]); let (h1, h0) = cl64(yh, &t[3..6]); let (m1, m0) = cl64(yh ^ yl, &t[6..9]);
        let (m1, m0) = (m1 ^ l1 ^ h1, m0 ^ l0 ^ h0);
        // 256-bit product X3:X2:X1:X0
        let (x3, x2, x1, x0) = (h1, h0 ^ m1, l1 ^ m0, l0);
        // shift left by one
        let (x3, x2, x1, x0) = ((x3 << 1) | (x2 >> 63), (x2 << 1) | (x1 >> 63), (x1 << 1) | (x0 >> 63), x0 << 1);
        let d = x1 ^ (x0 << 63) ^ (x0 << 62) ^ (x0 << 57);
        let e1 = d >> 1; let e0 = (x0 >> 1) | (d << 63);
        let f1 = d >> 2; let f0 = (x0 >> 2) | (d << 62);
        let g1 = d >> 7; let g0 = (x0 >> 7) | (d << 57);
        let hh1 = d ^ e1 ^ f1 ^ g1; let hh0 = x0 ^ e0 ^ f0 ^ g0;
        [x3 ^ hh1, x2 ^ hh0]
    }
    pub fn ghash(h: &[u8; 16], y: &mut [u8; 16], data: &[u8]) {
        let w = |b: &[u8]| [u64::from_be_bytes(b[0..8].try_into().unwrap()), u64::from_be_bytes(b[8..16].try_into().unwrap())];
        let t = prep(w(h)); let mut acc = w(y);
        for blk in data.chunks_exact(16) { let x = w(blk); acc = mul([acc[0] ^ x[0], acc[1] ^ x[1]], &t); }
        y[0..8].copy_from_slice(&acc[0].to_be_bytes()); y[8..16].copy_from_slice(&acc[1].to_be_bytes());
    }
}

#[allow(dead_code)]
pub mod proto2 {
    use super::proto::{cl32, split};
    /// polyMul(x, y) for 64-bit words: (low, high).
    fn pm(x: u64, t: &[[u64; 4]]) -> (u64, u64) {
        let (x1, x0) = (x >> 32, (x << 32) >> 32);
        let l = cl32(x0, t[0]); let h = cl32(x1, t[1]); let m = cl32(x0 ^ x1, t[2]) ^ l ^ h;
        (l ^ (m << 32), h ^ (m >> 32))
    }
    fn prep1(x: u64) -> [[u64; 4]; 3] { let (x1, x0) = (x >> 32, (x << 32) >> 32); [split(x0), split(x1), split(x0 ^ x1)] }
    const POLY: u64 = 0xc2 << 56;
    pub fn key(hi: u64, lo: u64) -> [[u64; 4]; 9] {
        let m = 0u64.wrapping_sub(hi >> 63) & POLY;
        let tp0 = (hi << 1) ^ (lo >> 63) ^ m; let tp1 = (lo << 1) ^ (hi >> 63);
        let (t0, t1) = (tp1, tp0);
        let [a, b, c] = prep1(t0); let [d, e, f] = prep1(t1); let [g, h, i] = prep1(t0 ^ t1);
        [a, b, c, d, e, f, g, h, i]
    }
    pub fn mul(a0: u64, a1: u64, k: &[[u64; 4]; 9]) -> (u64, u64) {
        let (lo0, lo1) = pm(a1, &k[0..3]);
        let (hi0, hi1) = pm(a0, &k[3..6]);
        let (k0, k1) = pm(a0 ^ a1, &k[6..9]);
        let (mid0, mid1) = (k0 ^ lo0 ^ hi0, k1 ^ lo1 ^ hi1);
        let u0 = mid0 ^ lo1 ^ (lo0 << 57) ^ (lo0 << 62) ^ (lo0 << 63);
        let u1 = mid1 ^ lo0 ^ (lo0 >> 7) ^ (lo0 >> 2) ^ (lo0 >> 1);
        (hi1 ^ u0 ^ (u0 >> 7) ^ (u0 >> 2) ^ (u0 >> 1), hi0 ^ u1 ^ (u0 << 57) ^ (u0 << 62) ^ (u0 << 63))
    }
    pub fn ghash(h: &[u8; 16], y: &mut [u8; 16], data: &[u8]) {
        let w = |b: &[u8]| (u64::from_be_bytes(b[0..8].try_into().unwrap()), u64::from_be_bytes(b[8..16].try_into().unwrap()));
        let (hh, hl) = w(h); let k = key(hh, hl); let (mut y0, mut y1) = w(y);
        for blk in data.chunks_exact(16) { let (x0, x1) = w(blk); (y0, y1) = mul(y0 ^ x0, y1 ^ x1, &k); }
        y[0..8].copy_from_slice(&y0.to_be_bytes()); y[8..16].copy_from_slice(&y1.to_be_bytes());
    }
}
