core::arch::global_asm!(include_str!("../ossl/mont.s"), options(att_syntax));
core::arch::global_asm!(include_str!("../ossl/mont5.s"), options(att_syntax));
core::arch::global_asm!(include_str!("../ossl/mont_r.s"), options(att_syntax));
core::arch::global_asm!(include_str!("../ossl/mont5_r.s"), options(att_syntax));
#[unsafe(no_mangle)]
pub static mut OPENSSL_ia32cap_P: [u32; 4] = [0, 0, (1 << 3) | (1 << 8) | (1 << 19), 0];
unsafe extern "C" {
    fn bn_mul_mont(rp: *mut u64, ap: *const u64, bp: *const u64, np: *const u64, n0: *const u64, num: i32) -> i32;
    fn bn_power5(rp: *mut u64, ap: *const u64, table: *const u64, np: *const u64, n0: *const u64, num: i32, power: i32);
    fn bn_mul_mont_r(rp: *mut u64, ap: *const u64, bp: *const u64, np: *const u64, n0: *const u64, num: i32) -> i32;
    fn bn_scatter5(inp: *const u64, num: usize, table: *mut u64, power: usize);
}
/// Cycles of OpenSSL's x86-64 Montgomery kernels (ADX paths), without the BN wrappers.
pub fn bench(w: usize, f: f64) {
    let mut s: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
    let mut n: Vec<u64> = (0..w).map(|_| rnd()).collect();
    n[0] |= 1; n[w - 1] |= 1 << 63;
    let mut inv: u64 = 1;
    for _ in 0..6 { inv = inv.wrapping_mul(2u64.wrapping_sub(n[0].wrapping_mul(inv))); }
    let n0 = [inv.wrapping_neg(), 0];
    let mut a: Vec<u64> = (0..w).map(|_| rnd()).collect(); a[w - 1] >>= 2;
    let mut b: Vec<u64> = (0..w).map(|_| rnd()).collect(); b[w - 1] >>= 2;
    let mut r = vec![0u64; w];
    // 64-byte aligned table of 32 entries
    let mut tab = vec![0u64; 32 * w + 8];
    let off = (8 - (tab.as_ptr() as usize / 8) % 8) % 8;
    for k in 0..32 { let e: Vec<u64> = (0..w).map(|_| rnd() >> 2).collect(); unsafe { bn_scatter5(e.as_ptr(), w, tab.as_mut_ptr().add(off), k) }; }
    let iters = 20000;
    let (mut sq, mut mu, mut p5, mut sqr) = (f64::MAX, f64::MAX, f64::MAX, f64::MAX);
    unsafe {
        for _ in 0..15 {
            let t = std::time::Instant::now();
            for _ in 0..iters { bn_mul_mont(r.as_mut_ptr(), a.as_ptr(), a.as_ptr(), n.as_ptr(), n0.as_ptr(), w as i32); }
            sq = sq.min(t.elapsed().as_nanos() as f64 / iters as f64);
            let t = std::time::Instant::now();
            for _ in 0..iters { bn_mul_mont_r(r.as_mut_ptr(), a.as_ptr(), a.as_ptr(), n.as_ptr(), n0.as_ptr(), w as i32); }
            sqr = sqr.min(t.elapsed().as_nanos() as f64 / iters as f64);
            let t = std::time::Instant::now();
            for _ in 0..iters { bn_mul_mont(r.as_mut_ptr(), a.as_ptr(), b.as_ptr(), n.as_ptr(), n0.as_ptr(), w as i32); }
            mu = mu.min(t.elapsed().as_nanos() as f64 / iters as f64);
            r.copy_from_slice(&a);
            let t = std::time::Instant::now();
            for k in 0..iters / 5 { bn_power5(r.as_mut_ptr(), r.as_ptr(), tab.as_ptr().add(off), n.as_ptr(), n0.as_ptr(), w as i32, (k % 32) as i32); }
            p5 = p5.min(t.elapsed().as_nanos() as f64 / (iters / 5) as f64);
        }
    }
    println!("w={w} openssl kernels: sq {:.0} cyc  sq-without-redc {:.0} cyc  mul {:.0} cyc  power5 {:.0} cyc ({:.0} cyc/bit)", sq * f, sqr * f, mu * f, p5 * f, p5 * f / 5.0);
}

pub fn sq1000(w: usize) {
    let mut s: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
    let mut n: Vec<u64> = (0..w).map(|_| rnd()).collect();
    n[0] |= 1; n[w - 1] |= 1 << 63;
    let mut inv: u64 = 1;
    for _ in 0..6 { inv = inv.wrapping_mul(2u64.wrapping_sub(n[0].wrapping_mul(inv))); }
    let n0 = [inv.wrapping_neg(), 0];
    let mut a: Vec<u64> = (0..w).map(|_| rnd()).collect(); a[w - 1] >>= 2;
    let mut r = vec![0u64; w];
    for _ in 0..1000 { unsafe { bn_mul_mont(r.as_mut_ptr(), a.as_ptr(), a.as_ptr(), n.as_ptr(), n0.as_ptr(), w as i32); } }
}
