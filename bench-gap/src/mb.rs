// Scratch: per-operation TSC timing, VG vs aws-lc, at a given modulus size.
use aws_lc_sys as s;
use core::arch::x86_64::_rdtsc;
unsafe extern "C" {
    #[link_name = "aws_lc_0_45_0_bn_mul_mont"]
    fn bn_mul_mont(rp: *mut u64, ap: *const u64, bp: *const u64, np: *const u64, n0: *const u64, num: i32) -> i32;
}
fn rnd(n: usize, seed: &mut u64) -> Vec<u8> {
    (0..n).map(|_| { *seed ^= *seed << 13; *seed ^= *seed >> 7; *seed ^= *seed << 17; *seed as u8 }).collect()
}
pub fn run(bits: usize) {
    let mut seed = 0x9e3779b97f4a7c15u64 ^ bits as u64;
    let mut p = rnd(bits / 8, &mut seed);
    p[0] |= 0xc0; *p.last_mut().unwrap() |= 1;
    let w = bits / 64;
    // aws-lc bn_mul_mont: little-endian words.
    let words = |b: &[u8]| -> Vec<u64> { (0..w).map(|i| { let mut x = 0u64; for j in 0..8 { x |= (b[b.len() - 1 - (8 * i + j)] as u64) << (8 * j); } x }).collect() };
    let np = words(&p);
    let mut inv = 1u64; for _ in 0..6 { inv = inv.wrapping_mul(2u64.wrapping_sub(np[0].wrapping_mul(inv))); }
    let n0 = [inv.wrapping_neg(), 0];
    let mut a = words(&rnd(bits / 8, &mut seed)); a[w - 1] >>= 2;
    let b = a.clone();
    let mut best = [u64::MAX; 2];
    for _ in 0..3000 {
        for k in 0..2 {
            let t = unsafe { _rdtsc() };
            for _ in 0..16 { unsafe {
                if k == 0 { bn_mul_mont(a.as_mut_ptr(), a.as_ptr(), a.as_ptr(), np.as_ptr(), n0.as_ptr(), w as i32); }
                else { bn_mul_mont(a.as_mut_ptr(), a.as_ptr(), b.as_ptr(), np.as_ptr(), n0.as_ptr(), w as i32); }
            } }
            best[k] = best[k].min((unsafe { _rdtsc() } - t) / 16);
        }
    }
    let mut vg = [u64::MAX; 4];
    for _ in 0..5 { let r = verified_garbage::ffdh::mb_hack(&p, 3000); for i in 0..4 { vg[i] = vg[i].min(r[i]); } }
    // Whole constant-time modexp with an exponent as long as the modulus.
    let e = rnd(bits / 8, &mut seed);
    let base = rnd(bits / 8 - 1, &mut seed);
    let modexp = unsafe {
        let bn = |v: &[u8]| s::BN_bin2bn(v.as_ptr(), v.len(), core::ptr::null_mut());
        let (m, x, ee, r) = (bn(&p), bn(&base), bn(&e), s::BN_new());
        let ctx = s::BN_CTX_new();
        let mont = s::BN_MONT_CTX_new_for_modulus(m, ctx);
        let mut bestm = u64::MAX;
        for _ in 0..300 {
            let t = _rdtsc();
            assert_eq!(s::BN_mod_exp_mont_consttime(r, x, ee, m, ctx, mont), 1);
            bestm = bestm.min(_rdtsc() - t);
        }
        bestm
    };
    println!("{bits}: aws sqr {} mul {} | vg strict sqr {} lazy sqr {} strict mul {} lazy mul {} | aws modexp {} (= {:.0} sqr-equivalents)",
        best[0], best[1], vg[0], vg[1], vg[2], vg[3], modexp, modexp as f64 / best[0] as f64);
}
