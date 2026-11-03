//! Local check of the unproven RISC-V Miller–Rabin round, prime search and
//! blinded loop (bench branch only), against Wycheproof's
//! `primality_test.json`, read from the checkout at `WYCHEPROOF_ROOT`.
#![cfg(target_arch = "riscv64")]

use verified_garbage_asm_riscv64::rsa_proto5::{
    vg_mr_blinded_hi_proto, vg_mr_blinded_proto, vg_mr_search_proto,
};

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn field(obj: &str, name: &str) -> Option<String> {
    let k = format!("\"{name}\"");
    let i = obj.find(&k)? + k.len();
    let rest = &obj[i..];
    let a = rest.find('"')? + 1;
    let b = rest[a..].find('"')? + a;
    Some(rest[a..b].to_string())
}

/// `(value, valid)` of every test: the value's big-endian bytes, as the file
/// has them (two's complement), and whether it is prime.
fn cases() -> Vec<(u32, Vec<u8>, String)> {
    let root = std::env::var("WYCHEPROOF_ROOT").expect("WYCHEPROOF_ROOT");
    let s = std::fs::read_to_string(format!("{root}/testvectors_v1/primality_test.json")).unwrap();
    let mut out = vec![];
    let mut at = 0;
    while let Some(i) = s[at..].find("\"tcId\"") {
        let start = at + i;
        let end = s[start..].find('}').unwrap() + start;
        let obj = &s[start..end];
        at = end;
        let id: u32 = obj["\"tcId\"".len()..]
            .trim_start_matches([' ', ':'])
            .split(',')
            .next()
            .unwrap()
            .trim()
            .parse()
            .unwrap();
        let v = field(obj, "value").unwrap();
        let r = field(obj, "result").unwrap();
        out.push((id, hex(&v), r));
    }
    out
}

struct Rng(u64);
impl Rng {
    fn byte(&mut self) -> u8 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 >> 24) as u8
    }
}

/// The positive, odd values of more than 64 bits, trimmed, and whether each is prime.
fn values() -> Vec<(u32, Vec<u8>, bool)> {
    cases()
        .into_iter()
        .filter_map(|(id, v, r)| {
            if v.is_empty() || v[0] & 0x80 != 0 || v.last().unwrap() & 1 == 0 {
                return None;
            }
            let i = v.iter().position(|&b| b != 0)?;
            let v = v[i..].to_vec();
            if v.len() < 9 {
                return None;
            }
            Some((id, v, r == "valid"))
        })
        .collect()
}

fn top_mask(c: &[u8]) -> u64 {
    let t = c.len().div_ceil(8) - 1;
    let hi = &c[..c.len() - 8 * t];
    let mut x = 0u64;
    for &b in hi {
        x = (x << 8) | u64::from(b);
    }
    if x >> 63 == 1 {
        u64::MAX
    } else {
        (1u64 << (64 - x.leading_zeros())) - 1
    }
}

type Fn8 =
    unsafe extern "C" fn(*const u8, usize, *const u8, usize, u64, usize, *mut u64, usize) -> u32;

fn run(f: Fn8, c: &[u8], checks: usize, seed: u64, draws: usize) -> u32 {
    let w = c.len().div_ceil(8).max(4);
    let mut ws = vec![0u64; 32 + 30 * (w + 2)];
    let mut rng = Rng(seed | 1);
    let tape: Vec<u8> = (0..draws * c.len()).map(|_| rng.byte()).collect();
    unsafe {
        f(
            c.as_ptr(),
            c.len(),
            tape.as_ptr(),
            tape.len(),
            top_mask(c),
            checks,
            ws.as_mut_ptr(),
            ws.len(),
        )
    }
}

fn check(name: &str, f: Fn8, draws: usize) {
    check_from(name, f, draws, 9)
}

fn check_from(name: &str, f: Fn8, draws: usize, min_len: usize) {
    let vs: Vec<_> = values()
        .into_iter()
        .filter(|v| v.1.len() >= min_len)
        .collect();
    assert!(vs.len() > 100, "{}", vs.len());
    let (mut primes, mut comps, mut by_round, mut round_fails) = (0, 0, 0, 0);
    for (id, c, valid) in &vs {
        let r = run(f, c, 8, 0x9e3779b97f4a7c15 ^ u64::from(*id), draws);
        if *valid {
            assert_eq!(r, 1, "{name}: tcId {id} is prime");
            primes += 1;
        } else {
            assert!(
                r & 16 != 0 || r & 15 == 2,
                "{name}: tcId {id} is composite, got {r}"
            );
            comps += 1;
            if r & 16 == 0 {
                by_round += 1;
            }
            if r & 15 == 2 {
                round_fails += 1;
            }
        }
    }
    eprintln!(
        "{name}: {primes} primes, {comps} composites, {by_round} past the sieve, {round_fails} failing a round"
    );
    assert!(by_round > 20);
}

#[test]
fn search() {
    check("search", vg_mr_search_proto, 2048);
}

/// `R² mod c` by `Precompute.r2`, for candidates whose top word is not zero
/// (at least 25 octets, so that `w = ⌈len / 8⌉ ≥ 4`).
#[test]
fn blinded_hi() {
    check_from("blinded_hi", vg_mr_blinded_hi_proto, 64, 25);
}

#[test]
fn blinded() {
    check("blinded", vg_mr_blinded_proto, 64);
}

/// The trial division and sieve alone must not reject a prime, and the
/// tests' result does not depend on the calls before.
#[test]
fn repeated() {
    let vs = values();
    let (_, p, _) = vs.iter().find(|v| v.2).unwrap();
    let a = run(vg_mr_search_proto, p, 3, 7, 512);
    let b = run(vg_mr_search_proto, p, 3, 7, 512);
    assert_eq!((a, b), (1, 1));
    // A tape too short for one witness: `hStat = 0`.
    assert_eq!(run(vg_mr_search_proto, p, 3, 7, 0), 0);
}
