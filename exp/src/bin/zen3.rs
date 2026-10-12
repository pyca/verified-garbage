use std::arch::x86_64::*;
use std::hint::black_box;

type Ks = [[u8; 16]; 11];

#[inline(always)]
unsafe fn key(ks: &Ks, j: usize) -> __m256i {
    _mm256_broadcastsi128_si256(_mm_loadu_si128(ks[j].as_ptr() as *const _))
}

#[inline(always)]
unsafe fn rounds<const N: usize>(x: &mut [__m256i; N], ks: &Ks) {
    let k = key(ks, 0);
    for r in x.iter_mut() { *r = _mm256_xor_si256(*r, k); }
    for j in 1..10 {
        let k = key(ks, j);
        for r in x.iter_mut() { *r = _mm256_aesenc_epi128(*r, k); }
    }
    let k = key(ks, 10);
    for r in x.iter_mut() { *r = _mm256_aesenclast_epi128(*r, k); }
}

fn gen(buf: &mut [u64; 64], n: usize, t: [u64; 2]) {
    let (mut lo, mut hi) = (t[0], t[1]);
    for i in 0..n {
        buf[2 * i] = lo; buf[2 * i + 1] = hi;
        let m = 0x87u64 & ((hi as i64 >> 63) as u64);
        hi = (hi << 1) | (lo >> 63); lo = (lo << 1) ^ m;
    }
}

#[inline(always)]
unsafe fn step<const S: i32, const R: i32>(tw: __m256i, c: __m256i) -> __m256i {
    _mm256_xor_si256(_mm256_slli_si256::<S>(tw), _mm256_clmulepi64_epi128::<0>(_mm256_srli_si256::<R>(tw), c))
}

// A: as emitted: tweaks in memory, 256-bit loads and stores, stepped after the group.
#[target_feature(enable = "avx2,vaes,aes,vpclmulqdq")]
unsafe fn a_mem256(ks: &Ks, t: [u64; 2], d: &mut [u8]) {
    let mut buf = [0u64; 64];
    gen(&mut buf, 16, t);
    let c = _mm256_set_epi64x(0, 0x87, 0, 0x87);
    let b = buf.as_mut_ptr() as *mut __m256i;
    for g in d.chunks_exact_mut(256) {
        let p = g.as_mut_ptr() as *mut __m256i;
        let mut x = [_mm256_setzero_si256(); 8];
        for k in 0..8 { x[k] = _mm256_xor_si256(_mm256_loadu_si256(p.add(k)), _mm256_loadu_si256(b.add(k))); }
        rounds(&mut x, ks);
        for k in 0..8 { _mm256_storeu_si256(p.add(k), _mm256_xor_si256(x[k], _mm256_loadu_si256(b.add(k)))); }
        for k in 0..8 { let tw = _mm256_loadu_si256(b.add(k)); _mm256_storeu_si256(b.add(k), step::<2, 14>(tw, c)); }
    }
}

#[inline(always)]
unsafe fn ld128(b: *const u64) -> __m256i {
    _mm256_inserti128_si256::<1>(_mm256_castsi128_si256(_mm_loadu_si128(b as *const _)), _mm_loadu_si128(b.add(2) as *const _))
}
#[inline(always)]
unsafe fn st128(b: *mut u64, v: __m256i) {
    _mm_storeu_si128(b as *mut _, _mm256_castsi256_si128(v));
    _mm_storeu_si128(b.add(2) as *mut _, _mm256_extracti128_si256::<1>(v));
}

// B: as A, with the tweaks stored and loaded 128 bits at a time.
#[target_feature(enable = "avx2,vaes,aes,vpclmulqdq")]
unsafe fn b_mem128(ks: &Ks, t: [u64; 2], d: &mut [u8]) {
    let mut buf = [0u64; 64];
    gen(&mut buf, 16, t);
    let c = _mm256_set_epi64x(0, 0x87, 0, 0x87);
    let b = buf.as_mut_ptr();
    for g in d.chunks_exact_mut(256) {
        let p = g.as_mut_ptr() as *mut __m256i;
        let mut x = [_mm256_setzero_si256(); 8];
        let mut tw = [_mm256_setzero_si256(); 8];
        for k in 0..8 { tw[k] = ld128(b.add(4 * k)); x[k] = _mm256_xor_si256(_mm256_loadu_si256(p.add(k)), tw[k]); }
        for k in 0..8 { st128(b.add(4 * k), step::<2, 14>(tw[k], c)); }
        rounds(&mut x, ks);
        for k in 0..8 { _mm256_storeu_si256(p.add(k), _mm256_xor_si256(x[k], tw[k])); }
    }
    // (B computes next before rounds, so the post xor must use old tweaks: fix by reloading old copies)
}

// C: eight blocks per group, the tweaks in four registers, stepped by alpha^8.
#[target_feature(enable = "avx2,vaes,aes,vpclmulqdq")]
unsafe fn c_reg8(ks: &Ks, t: [u64; 2], d: &mut [u8]) {
    let mut buf = [0u64; 64];
    gen(&mut buf, 8, t);
    let c = _mm256_set_epi64x(0, 0x87, 0, 0x87);
    let b = buf.as_ptr() as *const __m256i;
    let mut tw = [_mm256_setzero_si256(); 4];
    for k in 0..4 { tw[k] = _mm256_loadu_si256(b.add(k)); }
    for g in d.chunks_exact_mut(128) {
        let p = g.as_mut_ptr() as *mut __m256i;
        let mut x = [_mm256_setzero_si256(); 4];
        for k in 0..4 { x[k] = _mm256_xor_si256(_mm256_loadu_si256(p.add(k)), tw[k]); }
        rounds(&mut x, ks);
        for k in 0..4 { _mm256_storeu_si256(p.add(k), _mm256_xor_si256(x[k], tw[k])); tw[k] = step::<1, 15>(tw[k], c); }
    }
}

// D: sixteen blocks per group, the tweaks in eight registers (the compiler may spill).
#[target_feature(enable = "avx2,vaes,aes,vpclmulqdq")]
unsafe fn d_reg16(ks: &Ks, t: [u64; 2], d: &mut [u8]) {
    let mut buf = [0u64; 64];
    gen(&mut buf, 16, t);
    let c = _mm256_set_epi64x(0, 0x87, 0, 0x87);
    let b = buf.as_ptr() as *const __m256i;
    let mut tw = [_mm256_setzero_si256(); 8];
    for k in 0..8 { tw[k] = _mm256_loadu_si256(b.add(k)); }
    for g in d.chunks_exact_mut(256) {
        let p = g.as_mut_ptr() as *mut __m256i;
        let mut x = [_mm256_setzero_si256(); 8];
        for k in 0..8 { x[k] = _mm256_xor_si256(_mm256_loadu_si256(p.add(k)), tw[k]); }
        rounds(&mut x, ks);
        for k in 0..8 { _mm256_storeu_si256(p.add(k), _mm256_xor_si256(x[k], tw[k])); tw[k] = step::<2, 14>(tw[k], c); }
    }
}

// E: sixteen blocks, two tweak buffers: the next group's computed at the start of this one.
#[target_feature(enable = "avx2,vaes,aes,vpclmulqdq")]
unsafe fn e_dbl(ks: &Ks, t: [u64; 2], d: &mut [u8]) {
    let mut buf = [0u64; 64];
    gen(&mut buf, 16, t);
    let c = _mm256_set_epi64x(0, 0x87, 0, 0x87);
    let mut cur = buf.as_mut_ptr() as *mut __m256i;
    let mut nxt = cur.add(8);
    for g in d.chunks_exact_mut(256) {
        let p = g.as_mut_ptr() as *mut __m256i;
        let mut x = [_mm256_setzero_si256(); 8];
        for k in 0..8 {
            let tw = _mm256_loadu_si256(cur.add(k));
            x[k] = _mm256_xor_si256(_mm256_loadu_si256(p.add(k)), tw);
            _mm256_storeu_si256(nxt.add(k), step::<2, 14>(tw, c));
        }
        rounds(&mut x, ks);
        for k in 0..8 { _mm256_storeu_si256(p.add(k), _mm256_xor_si256(x[k], _mm256_loadu_si256(cur.add(k)))); }
        core::mem::swap(&mut cur, &mut nxt);
    }
}

// F: AES-NI only, 8 xmm blocks, tweaks in registers (OpenSSL-like), alpha^8 step with pclmulqdq.
#[target_feature(enable = "avx2,aes,pclmulqdq")]
unsafe fn f_xmm8(ks: &Ks, t: [u64; 2], d: &mut [u8]) {
    let mut buf = [0u64; 64];
    gen(&mut buf, 8, t);
    let c = _mm_set_epi64x(0, 0x87);
    let mut tw = [_mm_setzero_si128(); 8];
    for k in 0..8 { tw[k] = _mm_loadu_si128(buf.as_ptr().add(2 * k) as *const _); }
    for g in d.chunks_exact_mut(128) {
        let p = g.as_mut_ptr() as *mut __m128i;
        let mut x = [_mm_setzero_si128(); 8];
        for k in 0..8 { x[k] = _mm_xor_si128(_mm_loadu_si128(p.add(k)), tw[k]); }
        let k0 = _mm_loadu_si128(ks[0].as_ptr() as *const _);
        for r in x.iter_mut() { *r = _mm_xor_si128(*r, k0); }
        for j in 1..10 { let kj = _mm_loadu_si128(ks[j].as_ptr() as *const _); for r in x.iter_mut() { *r = _mm_aesenc_si128(*r, kj); } }
        let kl = _mm_loadu_si128(ks[10].as_ptr() as *const _);
        for r in x.iter_mut() { *r = _mm_aesenclast_si128(*r, kl); }
        for k in 0..8 {
            _mm_storeu_si128(p.add(k), _mm_xor_si128(x[k], tw[k]));
            tw[k] = _mm_xor_si128(_mm_slli_si128::<1>(tw[k]), _mm_clmulepi64_si128::<0>(_mm_srli_si128::<15>(tw[k]), c));
        }
    }
}

fn main() {
    let ks: Ks = core::array::from_fn(|i| [i as u8 * 17 + 3; 16]);
    let t = [0x0123456789abcdefu64, 0xfedcba9876543210u64];
    let d0: Vec<u8> = (0..16384).map(|i| (i * 7) as u8).collect();
    let mut d = d0.clone();
    let fs: [(&str, unsafe fn(&Ks, [u64; 2], &mut [u8])); 6] = [
        ("A mem256 (emitted)", a_mem256), ("B mem128", b_mem128), ("C reg8 ymm", c_reg8),
        ("D reg16 ymm", d_reg16), ("E double buffer", e_dbl), ("F xmm8 aes-ni", f_xmm8)];
    let mut r0 = d0.clone();
    unsafe { a_mem256(&ks, t, &mut r0) };
    for (name, f) in fs {
        let mut r = d0.clone();
        unsafe { f(&ks, t, &mut r) };
        let ok = r == r0;
        let mut best = f64::MAX;
        for _ in 0..40 {
            let t0 = std::time::Instant::now();
            for _ in 0..2000 { unsafe { f(black_box(&ks), black_box(t), black_box(&mut d)) } }
            best = best.min(t0.elapsed().as_nanos() as f64 / 2000.0);
        }
        println!("{name:20} {best:7.0} ns / 16 KiB  {}", if ok { "" } else { "(output differs)" });
    }
}
