#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto2::vg_rsa_private_crt;
fn hex(s: &str) -> Vec<u8> { (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect() }
fn num(ws: &[u64]) -> String { ws.iter().rev().map(|w| format!("{w:016x}")).collect() }
#[test]
fn dump() {
    let line = std::fs::read_to_string(std::env::var("CRT_CASES").unwrap()).unwrap();
    let line = line.lines().nth(std::env::var("CASE").map(|s| s.parse().unwrap()).unwrap_or(0)).unwrap();
    let f: Vec<Vec<u8>> = line.split(' ').map(hex).collect();
    let (n, c, p, q, dp, dq, qi) = (&f[0], &f[2], &f[3], &f[4], &f[5], &f[6], &f[7]);
    let k = n.len();
    let mut s = vec![0u64; 16 * k + 64];
    let mut out = vec![0u8; k];
    let r = unsafe { vg_rsa_private_crt(out.as_mut_ptr(), k, n.as_ptr(), k, c.as_ptr(), k, p.as_ptr(), p.len(), q.as_ptr(), q.len(), dp.as_ptr(), dp.len(), dq.as_ptr(), dq.len(), qi.as_ptr(), qi.len(), s.as_mut_ptr(), s.len()) };
    let base = s.as_ptr() as u64;
    let bw = |o: usize| ((s[o] - base) / 8) as usize;
    let ww = 2 * k.div_ceil(8);
    let wp = p.len().div_ceil(8).max(2);
    let wq = q.len().div_ceil(8).max(2);
    println!("r {r}");
    println!("mask {:x}", s[11]);
    for j in 0..8 { println!("X{j} {}", num(&s[32 + j * (ww + 2)..32 + j * (ww + 2) + ww])); }
    let bp = bw(12); let bq = bw(13);
    for j in 0..24 { println!("P{j} {}", num(&s[bp + 32 + j * (wp + 2)..bp + 32 + j * (wp + 2) + wp])); }
    for j in 0..24 { println!("Q{j} {}", num(&s[bq + 32 + j * (wq + 2)..bq + 32 + j * (wq + 2) + wq])); }
    println!("bp {} bq {} len {}", bp, bq, s.len());
}
