macro_rules! variant {
    ($name:ident, $file:literal) => {
        core::arch::global_asm!(concat!(".p2align 6\n.globl ", stringify!($name), "\n", stringify!($name), ":\n"), include_str!($file));
        unsafe extern "sysv64" { fn $name(ws: *mut u64, n: usize, o: u32, a: u32, b: u32); }
    };
}
include!("variants.rs");

fn setup(w: usize) -> (Vec<u64>, usize) {
    let n = 32 + 8 * (w + 2);
    let mut ws = vec![0u64; n];
    ws[6] = w as u64;
    let mut s: u64 = 0x1234_5678_9abc_def1;
    let mut rnd = || { s ^= s << 13; s ^= s >> 7; s ^= s << 17; s };
    for i in 0..8 { ws[8 + i] = (ws.as_ptr() as u64) + 8 * (32 + (i * (w + 2)) as u64); }
    for j in 0..w { ws[32 + j] = rnd(); }
    ws[32] |= 1; ws[32 + w - 1] |= 1 << 63;
    let m0 = ws[32];
    let mut inv: u64 = 1;
    for _ in 0..6 { inv = inv.wrapping_mul(2u64.wrapping_sub(m0.wrapping_mul(inv))); }
    ws[7] = inv.wrapping_neg();
    for a in 4..6 { for j in 0..w - 1 { ws[32 + a * (w + 2) + j] = rnd(); } }
    (ws, n)
}
fn ghz() -> f64 {
    let n: u64 = 300_000_000;
    let t = std::time::Instant::now();
    unsafe { core::arch::asm!("2: imul {x}, {x}", "imul {x}, {x}", "imul {x}, {x}", "imul {x}, {x}", "sub {n}, 4", "jnz 2b", x = inout(reg) 3u64 => _, n = inout(reg) n => _); }
    3.0 * n as f64 / t.elapsed().as_nanos() as f64
}
type F = unsafe extern "sysv64" fn(*mut u64, usize, u32, u32, u32);
fn time(f: F, w: usize, sq: bool, iters: usize) -> f64 {
    let (mut ws, n) = setup(w);
    let b = if sq { 4 } else { 5 };
    for _ in 0..iters / 10 { unsafe { f(ws.as_mut_ptr(), n, 4, 4, b) } }
    let mut best = f64::MAX;
    for _ in 0..2 {
        let t = std::time::Instant::now();
        for _ in 0..iters { unsafe { f(ws.as_mut_ptr(), n, 4, 4, b) } }
        best = best.min(t.elapsed().as_nanos() as f64 / iters as f64);
    }
    best
}
fn check(f: F, g: F, w: usize) {
    for sq in [true, false] {
        let (mut a, n) = setup(w); let (mut b, _) = setup(w);
        let bb = if sq { 4 } else { 5 };
        for _ in 0..50 { unsafe { f(a.as_mut_ptr(), n, 4, 4, bb); g(b.as_mut_ptr(), n, 4, 4, bb); } }
        let o = 32 + 4 * (w + 2);
        assert_eq!(&a[o..o + w], &b[o..o + w], "mismatch w={w} sq={sq}");
    }
}
fn main() {
    let f = ghz().max(ghz());
    println!("ghz {f:.2}");
    micro(f);
    let vs = variants();
    for w in [16usize, 24, 32] {
        let vs: Vec<_> = vs.iter().filter(|(n, _)| !(n.contains("blk16") && w % 16 != 0)).cloned().collect();
        for (name, v) in &vs { if !name.contains("only") { check(vs[0].1, *v, w); } }
        let mut best = vec![(f64::MAX, f64::MAX); vs.len()];
        for _ in 0..15 {
            for (k, (_, v)) in vs.iter().enumerate() {
                let s = time(*v, w, true, 20000); let m = time(*v, w, false, 20000);
                best[k].0 = best[k].0.min(s); best[k].1 = best[k].1.min(m);
            }
        }
        for (k, (name, _)) in vs.iter().enumerate() {
            println!("w={w} {name}: sq {:.0} cyc  mul {:.0} cyc", best[k].0 * f, best[k].1 * f);
        }
    }
}
macro_rules! micro_v { ($($n:ident),*) => { $(core::arch::global_asm!(concat!(".p2align 6\n.globl ", stringify!($n), "\n", stringify!($n), ":\n"), include_str!(concat!("../variants/", stringify!($n), ".s")));)* unsafe extern "sysv64" { $(fn $n(p: *const u64, n: usize);)* } fn micros() -> Vec<(&'static str, unsafe extern "sysv64" fn(*const u64, usize), f64)> { vec![$((stringify!($n), $n as unsafe extern "sysv64" fn(*const u64, usize), 1.0)),*] } } }
micro_v!(core_loop, mulx_only, adx16, adc16, adxm16, redcblk, redcblk_ld);
pub fn micro(f: f64) {
    let mut buf = [7u64; 64];
    for (name, g, _) in micros() {
        let n = 20_000_000;
        let mut best = f64::MAX;
        for _ in 0..3 { let t = std::time::Instant::now(); unsafe { g(buf.as_mut_ptr(), n) }; best = best.min(t.elapsed().as_nanos() as f64 * f / n as f64); }
        println!("micro {name}: {best:.2} cyc/iter");
    }
}
