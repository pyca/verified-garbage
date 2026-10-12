use std::arch::x86_64::*;
use std::hint::black_box;

type Ks = [[u8; 16]; 11];

fn gen(buf: &mut [u64; 64], n: usize, t: [u64; 2]) {
    let (mut lo, mut hi) = (t[0], t[1]);
    for i in 0..n {
        buf[2 * i] = lo; buf[2 * i + 1] = hi;
        let m = 0x87u64 & ((hi as i64 >> 63) as u64);
        hi = (hi << 1) | (lo >> 63); lo = (lo << 1) ^ m;
    }
}

// Round keys loaded from memory each round, as the emitted code does.
#[inline(always)]
unsafe fn rk(ks: &Ks, j: usize) -> __m128i { _mm_loadu_si128(black_box(ks[j].as_ptr()) as *const _) }

#[inline(always)]
unsafe fn rounds<const N: usize>(x: &mut [__m128i; N], ks: &Ks) {
    let k = rk(ks, 0);
    for r in x.iter_mut() { *r = _mm_xor_si128(*r, k); }
    for j in 1..10 { let k = rk(ks, j); for r in x.iter_mut() { *r = _mm_aesenc_si128(*r, k); } }
    let k = rk(ks, 10);
    for r in x.iter_mut() { *r = _mm_aesenclast_si128(*r, k); }
}

#[inline(always)]
unsafe fn step<const S: i32, const R: i32>(t: __m128i, c: __m128i) -> __m128i {
    _mm_xor_si128(_mm_slli_si128::<S>(t), _mm_clmulepi64_si128::<0>(_mm_srli_si128::<R>(t), c))
}

// G: 8 blocks, tweaks in a buffer with 128-bit loads and stores, stepped by alpha^8 after the group.
#[target_feature(enable = "avx,aes,pclmulqdq")]
unsafe fn g_mem8(ks: &Ks, t: [u64; 2], d: &mut [u8]) {
    let mut buf = [0u64; 64];
    gen(&mut buf, 8, t);
    let c = _mm_set_epi64x(0, 0x87);
    let b = buf.as_mut_ptr() as *mut __m128i;
    for g in d.chunks_exact_mut(128) {
        let p = g.as_mut_ptr() as *mut __m128i;
        let mut x = [_mm_setzero_si128(); 8];
        for k in 0..8 { x[k] = _mm_xor_si128(_mm_loadu_si128(p.add(k)), _mm_loadu_si128(b.add(k))); }
        rounds(&mut x, ks);
        for k in 0..8 { _mm_storeu_si128(p.add(k), _mm_xor_si128(x[k], _mm_loadu_si128(b.add(k)))); }
        for k in 0..8 { let tw = _mm_loadu_si128(b.add(k)); _mm_storeu_si128(b.add(k), step::<1, 15>(tw, c)); }
    }
}

// H: 6 blocks, tweaks in registers, the next six from the last one with the scalar-style doubling in xmm
// (as OpenSSL's aesni_xts): each tweak is the previous times alpha.
#[inline(always)]
unsafe fn mul_a(t: __m128i) -> __m128i {
    // t << 1 across 128 bits, xor 0x87 if the top bit was set.
    let hi = _mm_srai_epi32::<31>(_mm_shuffle_epi32::<0x13>(t));
    let m = _mm_and_si128(hi, _mm_set_epi32(0, 1, 0, 0x87));
    _mm_xor_si128(_mm_add_epi64(t, t), m)
}
#[target_feature(enable = "avx,aes,pclmulqdq")]
unsafe fn h_reg6(ks: &Ks, t: [u64; 2], d: &mut [u8]) {
    let mut buf = [0u64; 64];
    gen(&mut buf, 1, t);
    let mut tw = _mm_loadu_si128(buf.as_ptr() as *const _);
    let n6 = d.len() / 96 * 96;
    for g in d[..n6].chunks_exact_mut(96) {
        let p = g.as_mut_ptr() as *mut __m128i;
        let mut ts = [_mm_setzero_si128(); 6];
        for k in 0..6 { ts[k] = tw; tw = mul_a(tw); }
        let mut x = [_mm_setzero_si128(); 6];
        for k in 0..6 { x[k] = _mm_xor_si128(_mm_loadu_si128(p.add(k)), ts[k]); }
        rounds(&mut x, ks);
        for k in 0..6 { _mm_storeu_si128(p.add(k), _mm_xor_si128(x[k], ts[k])); }
    }
    for blk in d[n6..].chunks_exact_mut(16) {
        let p = blk.as_mut_ptr() as *mut __m128i;
        let mut x = [_mm_xor_si128(_mm_loadu_si128(p), tw)];
        rounds(&mut x, ks);
        _mm_storeu_si128(p, _mm_xor_si128(x[0], tw));
        tw = mul_a(tw);
    }
}

// F: 8 blocks, tweaks in (spilled) registers, stepped by alpha^8.
#[target_feature(enable = "avx,aes,pclmulqdq")]
unsafe fn f_reg8(ks: &Ks, t: [u64; 2], d: &mut [u8]) {
    let mut buf = [0u64; 64];
    gen(&mut buf, 8, t);
    let c = _mm_set_epi64x(0, 0x87);
    let mut tw = [_mm_setzero_si128(); 8];
    for k in 0..8 { tw[k] = _mm_loadu_si128(buf.as_ptr().add(2 * k) as *const _); }
    for g in d.chunks_exact_mut(128) {
        let p = g.as_mut_ptr() as *mut __m128i;
        let mut x = [_mm_setzero_si128(); 8];
        for k in 0..8 { x[k] = _mm_xor_si128(_mm_loadu_si128(p.add(k)), tw[k]); }
        rounds(&mut x, ks);
        for k in 0..8 { _mm_storeu_si128(p.add(k), _mm_xor_si128(x[k], tw[k])); tw[k] = step::<1, 15>(tw[k], c); }
    }
}

fn main() {
    let ks: Ks = core::array::from_fn(|i| [i as u8 * 17 + 3; 16]);
    let t = [0x0123456789abcdefu64, 0xfedcba9876543210u64];
    let d0: Vec<u8> = (0..16384).map(|i| (i * 7) as u8).collect();
    let mut d = d0.clone();
    let fs: [(&str, unsafe fn(&Ks, [u64; 2], &mut [u8])); 3] =
        [("G mem128 x8", g_mem8), ("H reg x6 (OpenSSL-like)", h_reg6), ("F reg x8 (spills)", f_reg8)];
    let mut r0 = d0.clone();
    unsafe { g_mem8(&ks, t, &mut r0) };
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
        println!("{name:26} {best:7.0} ns / 16 KiB {}", if ok { "" } else { "(output differs)" });
    }
}
