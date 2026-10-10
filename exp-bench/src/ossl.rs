use openssl_sys as ffi;
use std::ptr;
unsafe extern "C" {
    fn BN_MONT_CTX_new() -> *mut ffi::BN_MONT_CTX;
    fn BN_MONT_CTX_set(m: *mut ffi::BN_MONT_CTX, n: *const ffi::BIGNUM, ctx: *mut ffi::BN_CTX) -> i32;
    fn BN_mod_mul_montgomery(r: *mut ffi::BIGNUM, a: *const ffi::BIGNUM, b: *const ffi::BIGNUM, m: *mut ffi::BN_MONT_CTX, ctx: *mut ffi::BN_CTX) -> i32;
    fn BN_rand(r: *mut ffi::BIGNUM, bits: i32, top: i32, bottom: i32) -> i32;
    fn BN_mod_exp_mont_consttime(r: *mut ffi::BIGNUM, a: *const ffi::BIGNUM, p: *const ffi::BIGNUM, m: *const ffi::BIGNUM, ctx: *mut ffi::BN_CTX, mont: *mut ffi::BN_MONT_CTX) -> i32;
}
/// Cycles per OpenSSL Montgomery square and product of `w` words, and per bit of a constant-time exponentiation.
pub fn bench(w: usize, f: f64) {
    unsafe {
        let ctx = ffi::BN_CTX_new();
        let n = ffi::BN_new(); let a = ffi::BN_new(); let b = ffi::BN_new(); let r = ffi::BN_new(); let e = ffi::BN_new();
        let bits = (64 * w) as i32;
        BN_rand(n, bits, 1, 1); BN_rand(a, bits - 1, 0, 0); BN_rand(b, bits - 1, 0, 0); BN_rand(e, bits, 1, 1);
        let m = BN_MONT_CTX_new(); BN_MONT_CTX_set(m, n, ctx);
        let iters = 20000;
        let mut sq = f64::MAX; let mut mu = f64::MAX;
        for _ in 0..15 {
            let t = std::time::Instant::now();
            for _ in 0..iters { BN_mod_mul_montgomery(r, a, a, m, ctx); }
            sq = sq.min(t.elapsed().as_nanos() as f64 / iters as f64);
            let t = std::time::Instant::now();
            for _ in 0..iters { BN_mod_mul_montgomery(r, a, b, m, ctx); }
            mu = mu.min(t.elapsed().as_nanos() as f64 / iters as f64);
        }
        let mut ex = f64::MAX;
        for _ in 0..5 {
            let t = std::time::Instant::now();
            for _ in 0..20 { BN_mod_exp_mont_consttime(r, a, e, n, ctx, m); }
            ex = ex.min(t.elapsed().as_nanos() as f64 / 20.0);
        }
        println!("w={w} openssl: sq {:.0} cyc  mul {:.0} cyc  modexp {:.0} cyc/bit", sq * f, mu * f, ex * f / bits as f64);
        let _ = ptr::null::<u8>();
    }
}
