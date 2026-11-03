//! Local check of Proto14 (bench branch only): the narrow division and the short carry
//! chain give main's results: `check_key`'s mask on Wycheproof's keys (`key_cases.txt`)
//! and corrupted ones, and `crt_values`' outputs on those keys and on random `p`, `q`
//! (`n = p q`) and `d`, of lengths not a multiple of 8 and with top words of 1.
#![cfg(target_arch = "riscv64")]
use verified_garbage_asm_riscv64::rsa_proto14::*;

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn cases() -> Vec<Vec<Vec<u8>>> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/key_cases.txt");
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .map(|l| l.split(' ').map(hex).collect())
        .collect()
}

type Key = unsafe extern "C" fn(
    *const u8, usize, *const u8, usize, *const u8, usize, *const u8, usize, *const u8, usize,
    *const u8, usize, *const u8, usize, *const u8, usize, *mut u64, usize,
) -> u32;
type Crt = unsafe extern "C" fn(
    *mut u8, usize, *mut u8, usize, *mut u8, usize, *const u8, usize, *const u8, usize,
    *const u8, usize, *const u8, usize, *mut u64, usize,
) -> u32;

fn key(f: Key, g: &[Vec<u8>]) -> u32 {
    let mut s = vec![0x5a5a5a5a5a5a5a5au64; 16 * g[0].len() + 32];
    unsafe {
        f(
            g[0].as_ptr(), g[0].len(), g[1].as_ptr(), g[1].len(), g[2].as_ptr(), g[2].len(),
            g[3].as_ptr(), g[3].len(), g[4].as_ptr(), g[4].len(), g[5].as_ptr(), g[5].len(),
            g[6].as_ptr(), g[6].len(), g[7].as_ptr(), g[7].len(), s.as_mut_ptr(), s.len(),
        )
    }
}

/// `(mask, dP, dQ, qInv)` from `n`, `p`, `q`, `d`.
fn crt(f: Crt, n: &[u8], p: &[u8], q: &[u8], d: &[u8]) -> (u32, Vec<u8>, Vec<u8>, Vec<u8>) {
    let mut s = vec![0x5a5a5a5a5a5a5a5au64; 16 * n.len() + 32];
    let (mut dp, mut dq, mut qi) = (vec![0x77; p.len()], vec![0x77; q.len()], vec![0x77; p.len()]);
    let m = unsafe {
        f(
            dp.as_mut_ptr(), dp.len(), dq.as_mut_ptr(), dq.len(), qi.as_mut_ptr(), qi.len(),
            n.as_ptr(), n.len(), p.as_ptr(), p.len(), q.as_ptr(), q.len(), d.as_ptr(), d.len(),
            s.as_mut_ptr(), s.len(),
        )
    };
    (m, dp, dq, qi)
}

fn variants(f: &[Vec<u8>]) -> Vec<(String, Vec<Vec<u8>>)> {
    let mut v = vec![("key".to_string(), f.to_vec())];
    for i in 0..8 {
        let l = f[i].len();
        for (j, m) in [(l - 1, 1u8), (l - 1, 2), (0, 1)] {
            let mut g = f.to_vec();
            g[i][j] ^= m;
            v.push((format!("field {i} byte {j} ^ {m}"), g));
        }
    }
    let mut g = f.to_vec();
    g.swap(3, 4);
    g.swap(5, 6);
    if g[3].len() == g[7].len() {
        v.push(("p, q swapped".to_string(), g));
    }
    v
}

const KEYS: [(&str, Key); 3] = [
    ("a", vg_p14_check_key_a),
    ("b", vg_p14_check_key_b),
    ("c", vg_p14_check_key_c),
];
const CRTS: [(&str, Crt); 3] = [
    ("a", vg_p14_crt_values_a),
    ("b", vg_p14_crt_values_b),
    ("c", vg_p14_crt_values_c),
];

#[test]
fn check_key_same_masks() {
    let (mut n, mut ones) = (0, 0);
    for f in cases() {
        for (name, g) in variants(&f) {
            let base = key(vg_p14_check_key_base, &g);
            for (v, k) in KEYS {
                assert_eq!(base, key(k, &g), "{v}: k = {}, {name}", f[0].len());
            }
            if name == "key" {
                assert_eq!(base, 1);
            }
            n += 1;
            ones += base;
        }
    }
    eprintln!("check_key: {n} variants, {ones} accepted");
}

#[test]
fn crt_values_keys() {
    let mut n = 0;
    for f in cases() {
        for (name, g) in variants(&f) {
            let base = crt(vg_p14_crt_values_base, &g[0], &g[3], &g[4], &g[2]);
            for (v, c) in CRTS {
                assert_eq!(base, crt(c, &g[0], &g[3], &g[4], &g[2]), "{v}: {name}");
            }
            if name == "key" {
                assert_eq!(base, (1, g[5].clone(), g[6].clone(), g[7].clone()));
            }
            n += 1;
        }
    }
    eprintln!("crt_values: {n} key variants");
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next() as u8).collect()
    }
}

/// Big-endian product.
fn mul(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut r = vec![0u32; a.len() + b.len()];
    for (i, &x) in a.iter().rev().enumerate() {
        let mut c = 0u32;
        for (j, &y) in b.iter().rev().enumerate() {
            let t = r[i + j] + x as u32 * y as u32 + c;
            r[i + j] = t & 0xff;
            c = t >> 8;
        }
        r[i + b.len()] += c;
    }
    let mut v: Vec<u8> = r.iter().rev().map(|&x| x as u8).collect();
    while v.len() > 1 && v[0] == 0 {
        v.remove(0);
    }
    v
}

#[test]
fn crt_values_random() {
    let mut rng = Rng(0x9e3779b97f4a7c15);
    let (mut n, mut ok) = (0, 0);
    for pl in [33usize, 40, 41, 47, 49, 64, 65, 97, 100, 129] {
        for ql in [pl - 1, pl, pl + 1] {
            for top in [None, Some(1u8)] {
                for _ in 0..3 {
                    let mut p = rng.bytes(pl);
                    let mut q = rng.bytes(ql);
                    p[0] = top.unwrap_or(p[0] | 0x80);
                    q[0] |= 0x80;
                    p[pl - 1] |= 1;
                    q[ql - 1] |= 1;
                    let nn = mul(&p, &q);
                    if nn.len() < 64 {
                        continue;
                    }
                    for dl in [nn.len(), nn.len() - 3] {
                        let mut d = rng.bytes(dl);
                        d[0] |= 1;
                        let base = crt(vg_p14_crt_values_base, &nn, &p, &q, &d);
                        for (v, c) in CRTS {
                            assert_eq!(base, crt(c, &nn, &p, &q, &d), "{v}: pl {pl} ql {ql} dl {dl}");
                        }
                        n += 1;
                        ok += base.0;
                    }
                }
            }
        }
    }
    eprintln!("crt_values: {n} random cases, {ok} with mask 1");
    assert!(ok > n / 2);
}
