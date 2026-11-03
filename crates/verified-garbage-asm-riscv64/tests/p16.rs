//! Local check of Proto16 (bench branch only): `vg_rsa_public_precompute` with the
//! doublings started at `n`'s top bit and/or the squares by `sqrTail` gives main's
//! output (return value and all of `pre`) on Wycheproof's moduli (`key_cases.txt`) and
//! random moduli of every length and top byte, valid or not.
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto16::*;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

type Pre = unsafe extern "C" fn(*mut u64, usize, *const u8, usize, *mut u64, usize) -> u32;

fn pre(f: Pre, n: &[u8]) -> (u32, Vec<u64>) {
    let w = n.len().div_ceil(8);
    let mut s = vec![0x5a5a5a5a5a5a5a5au64; 8 * w + 48];
    let mut p = vec![0x77u64; 2 * w];
    let r = unsafe {
        f(
            p.as_mut_ptr(),
            p.len(),
            n.as_ptr(),
            n.len(),
            s.as_mut_ptr(),
            s.len(),
        )
    };
    (r, p)
}

const FS: [(&str, Pre); 3] = [
    ("top", vg_p16_precompute_top),
    ("sqr", vg_p16_precompute_sqr),
    ("both", vg_p16_precompute_both),
];

fn same(n: &[u8], what: &str) -> u32 {
    let base = pre(vg_p16_precompute_base, n);
    for (v, f) in FS {
        assert_eq!(base, pre(f, n), "{v}: {what}");
    }
    base.0
}

#[test]
fn precompute_keys() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/key_cases.txt");
    let mut k = 0;
    for l in std::fs::read_to_string(path).unwrap().lines() {
        let n = hex(l.split(' ').next().unwrap());
        assert_eq!(same(&n, "key"), 1);
        k += 1;
    }
    eprintln!("precompute: {k} Wycheproof moduli");
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

#[test]
fn precompute_random() {
    let mut r = Rng(0x9e3779b97f4a7c15);
    let (mut n_ok, mut n_all) = (0, 0);
    for len in (64..=520)
        .step_by(3)
        .chain([64, 65, 72, 128, 255, 256, 257, 384, 512, 513])
    {
        for top in [1u8, 2, 3, 0x7f, 0x80, 0xff, 0] {
            let mut n: Vec<u8> = (0..len).map(|_| r.next() as u8).collect();
            n[0] = if top == 0 { r.next() as u8 } else { top };
            if r.next() % 8 != 0 {
                n[len - 1] |= 1;
            }
            n_ok += same(&n, &format!("len {len} top {top}"));
            n_all += 1;
        }
    }
    eprintln!("precompute: {n_all} random moduli, {n_ok} valid");
}
