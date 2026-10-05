use std::hint::black_box;
use std::time::Instant;
#[cfg(target_os = "macos")]
core::arch::global_asm!(include_str!("funcs_macos.s"));
#[cfg(target_os = "macos")]
core::arch::global_asm!(include_str!("win_macos.s"));
#[cfg(not(target_os = "macos"))]
core::arch::global_asm!(include_str!("funcs_linux.s"));
#[cfg(not(target_os = "macos"))]
core::arch::global_asm!(include_str!("win_linux.s"));
unsafe extern "C" {
    fn p_w_dblW(a: *const u8, b: *const u8, c: *const u8, sc: *mut u64);
    fn p_w_dblW1(a: *const u8, b: *const u8, c: *const u8, sc: *mut u64);
    fn p_w_dblS(a: *const u8, b: *const u8, c: *const u8, sc: *mut u64);
    fn p_w_sel(a: *const u8, b: *const u8, c: *const u8, sc: *mut u64);
    fn p_w_addW(a: *const u8, b: *const u8, c: *const u8, sc: *mut u64);
    fn p_w_addS(a: *const u8, b: *const u8, c: *const u8, sc: *mut u64);
    fn p_verify_old(pk: *const u8, sig: *const u8, ch: *const u8, scratch: *mut u64) -> u32;
    fn p_verify_new(pk: *const u8, sig: *const u8, ch: *const u8, scratch: *mut u64) -> u32;
    fn p_scalar_base(out: *mut u8, s: *const u8, scratch: *mut u64);
    fn p_mul_add(out: *mut u8, r: *const u8, k: *const u8, s: *const u8, scratch: *mut u64);
    fn p_p1(pk: *const u8, sig: *const u8, ch: *const u8, scratch: *mut u64) -> u32;
    fn p_p2(pk: *const u8, sig: *const u8, ch: *const u8, scratch: *mut u64) -> u32;
    fn p_p3(pk: *const u8, sig: *const u8, ch: *const u8, scratch: *mut u64) -> u32;
    fn p_reduce(out: *mut u8, wide: *const u8, scratch: *mut u64);
}
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } fn bytes(&mut self, n: usize) -> Vec<u8> { (0..n).map(|_| self.next() as u8).collect() } }
fn scalar(rng: &mut Rng, sc: &mut [u64; 1024]) -> [u8; 57] { let w = rng.bytes(114); let mut o = [0u8; 57]; unsafe { p_reduce(o.as_mut_ptr(), w.as_ptr(), sc.as_mut_ptr()) }; o }
fn base(s: &[u8; 57], sc: &mut [u64; 1024]) -> [u8; 57] { let mut o = [0u8; 57]; unsafe { p_scalar_base(o.as_mut_ptr(), s.as_ptr(), sc.as_mut_ptr()) }; o }
fn vo(pk: &[u8], sig: &[u8], ch: &[u8], sc: &mut [u64; 1024]) -> u32 { unsafe { p_verify_old(pk.as_ptr(), sig.as_ptr(), ch.as_ptr(), sc.as_mut_ptr()) } }
fn vn(pk: &[u8], sig: &[u8], ch: &[u8], sc: &mut [u64; 1024]) -> u32 { unsafe { p_verify_new(pk.as_ptr(), sig.as_ptr(), ch.as_ptr(), sc.as_mut_ptr()) } }
fn main() {
    let mut rng = Rng(0x1234_5678_9abc_def1);
    let mut sc = Box::new([0u64; 1024]);
    let (mut ok, mut agree) = (0, 0);
    let mut last = (vec![], vec![], vec![]);
    for it in 0..200 {
        let a = scalar(&mut rng, &mut sc); let pk = base(&a, &mut sc);
        let r = scalar(&mut rng, &mut sc); let rr = base(&r, &mut sc);
        let k = scalar(&mut rng, &mut sc);
        let mut s = [0u8; 57]; unsafe { p_mul_add(s.as_mut_ptr(), r.as_ptr(), k.as_ptr(), a.as_ptr(), sc.as_mut_ptr()) };
        let mut sig = rr.to_vec(); sig.extend_from_slice(&s);
        let (o, n) = (vo(&pk, &sig, &k, &mut sc), vn(&pk, &sig, &k, &mut sc));
        assert_eq!(o, 1, "old rejects valid at {it}");
        if n == 1 { ok += 1 }
        // corruptions
        for c in 0..6 {
            let (mut pk2, mut sig2, mut k2) = (pk.to_vec(), sig.clone(), k.to_vec());
            let bit = (rng.next() % 8) as u8; let i = (rng.next() % 57) as usize;
            match c { 0 => pk2[i] ^= 1 << bit, 1 => sig2[i] ^= 1 << bit, 2 => sig2[57 + i] ^= 1 << bit, 3 => k2[i] ^= 1 << bit, 4 => sig2[113] = 1, _ => pk2[56] ^= 0x80 }
            let (o2, n2) = (vo(&pk2, &sig2, &k2, &mut sc), vn(&pk2, &sig2, &k2, &mut sc));
            if o2 == n2 { agree += 1 } else { println!("disagree it={it} c={c}: old={o2} new={n2}") }
        }
        last = (pk.to_vec(), sig, k.to_vec());
    }
    println!("valid accepted by new: {ok}/200; corruptions agree: {agree}/1200");
    let (pk, sig, k) = last;
    let t = |f: &dyn Fn(&mut [u64; 1024]) -> u32, sc: &mut [u64; 1024]| { let mut b = f64::MAX; for _ in 0..20 { let st = Instant::now(); for _ in 0..50 { black_box(f(sc)); } b = b.min(st.elapsed().as_secs_f64() / 50.0) } b * 1e6 };
    let to = t(&|sc| vo(black_box(&pk), &sig, &k, sc), &mut sc);
    let tn = t(&|sc| vn(black_box(&pk), &sig, &k, sc), &mut sc);
    println!("verify_equation: old {to:.1} us, new {tn:.1} us");
    let t1 = t(&|sc| unsafe { p_p1(black_box(pk.as_ptr()), sig.as_ptr(), k.as_ptr(), sc.as_mut_ptr()) }, &mut sc);
    let t2 = t(&|sc| unsafe { p_p2(black_box(pk.as_ptr()), sig.as_ptr(), k.as_ptr(), sc.as_mut_ptr()) }, &mut sc);
    let t3 = t(&|sc| unsafe { p_p3(black_box(pk.as_ptr()), sig.as_ptr(), k.as_ptr(), sc.as_mut_ptr()) }, &mut sc);
    for (nm, f) in [("4 dblW", p_w_dblW as unsafe extern "C" fn(*const u8,*const u8,*const u8,*mut u64)), ("4 dblW1", p_w_dblW1), ("4 dblS", p_w_dblS), ("sel", p_w_sel), ("addW", p_w_addW), ("addS", p_w_addS)] {
        let tt = t(&|sc| { unsafe { f(pk.as_ptr(), sig.as_ptr(), k.as_ptr(), sc.as_mut_ptr()) }; 0 }, &mut sc);
        println!("228 x {nm}: {tt:.1} us");
    }
    println!("entry+decode+finish {t1:.1}, +table {t2:.1}, +[S]B {t3:.1}, +windows {tn:.1}");
}
