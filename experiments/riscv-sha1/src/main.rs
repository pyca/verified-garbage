//! Throwaway experiment, never merged: checks and times the variants
//! `gen.py` writes to `src/variants.s` against the verified PBKDF2-HMAC-SHA-1.

use core::num::NonZeroU32;
use std::time::Instant;

use verified_garbage::hashes::sha1::Sha1;
use verified_garbage::pbkdf2::pbkdf2_hmac;

core::arch::global_asm!(include_str!("variants.s"));

type Iter = unsafe extern "C" fn(*mut u32, *mut u32, u64);

unsafe extern "C" {
    fn iter_v0(state: *mut u32, u: *mut u32, n: u64);
    fn iter_fold(state: *mut u32, u: *mut u32, n: u64);
    fn iter_fold_order(state: *mut u32, u: *mut u32, n: u64);
    fn iter_fold_dbl(state: *mut u32, u: *mut u32, n: u64);
    fn iter_fold_order_dbl(state: *mut u32, u: *mut u32, n: u64);
}

fn compress(h: &mut [u32; 5], block: &[u8; 64]) {
    let mut w = [0u32; 80];
    for i in 0..16 {
        w[i] = u32::from_be_bytes(block[4 * i..4 * i + 4].try_into().unwrap());
    }
    for i in 16..80 {
        w[i] = (w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1);
    }
    let [mut a, mut b, mut c, mut d, mut e] = *h;
    for (t, wt) in w.iter().enumerate() {
        let (f, k) = match t / 20 {
            0 => ((b & c) | (!b & d), 0x5A827999),
            1 => (b ^ c ^ d, 0x6ED9EBA1),
            2 => ((b & c) | (b & d) | (c & d), 0x8F1BBCDC),
            _ => (b ^ c ^ d, 0xCA62C1D6),
        };
        let x = a.rotate_left(5).wrapping_add(f).wrapping_add(e).wrapping_add(k).wrapping_add(*wt);
        (e, d, c, b, a) = (d, c, b.rotate_left(30), a, x);
    }
    for (hi, v) in h.iter_mut().zip([a, b, c, d, e]) {
        *hi = hi.wrapping_add(v);
    }
}

fn midstate(key: &[u8], pad: u8) -> [u32; 5] {
    let mut block = [pad; 64];
    for (b, k) in block.iter_mut().zip(key) {
        *b ^= k;
    }
    let mut h = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];
    compress(&mut h, &block);
    h
}

fn words(bytes: &[u8; 20]) -> [u32; 5] {
    core::array::from_fn(|i| u32::from_be_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap()))
}

fn run(f: Iter, pw: &[u8], salt: &[u8], n: u32) -> [u32; 5] {
    let mut u1 = [0u8; 20];
    pbkdf2_hmac::<Sha1>(pw, salt, NonZeroU32::new(1).unwrap(), &mut u1);
    let mut state = [0u32; 15];
    state[..5].copy_from_slice(&midstate(pw, 0x36));
    state[5..10].copy_from_slice(&midstate(pw, 0x5c));
    state[10..].copy_from_slice(&words(&u1));
    let mut u = words(&u1);
    unsafe { f(state.as_mut_ptr(), u.as_mut_ptr(), u64::from(n)) };
    state[10..].try_into().unwrap()
}

fn main() {
    let variants: [(&str, Iter); 5] = [
        ("v0", iter_v0),
        ("fold", iter_fold),
        ("fold_order", iter_fold_order),
        ("fold_dbl", iter_fold_dbl),
        ("fold_order_dbl", iter_fold_order_dbl),
    ];
    let (pw, salt) = (b"password-of-some-length", b"saltSALTsalt");
    for n in [1, 2, 3, 1000] {
        let mut expect = [0u8; 20];
        pbkdf2_hmac::<Sha1>(pw, salt, NonZeroU32::new(n + 1).unwrap(), &mut expect);
        for (name, f) in variants {
            assert_eq!(run(f, pw, salt, n), words(&expect), "{name}, n = {n}");
        }
    }
    println!("all variants match the verified PBKDF2");

    let n: u32 = std::env::args().nth(1).map_or(1 << 20, |s| s.parse().unwrap());
    let reps = 5;
    let time = |f: &dyn Fn()| {
        (0..reps)
            .map(|_| {
                let t = Instant::now();
                f();
                t.elapsed().as_secs_f64()
            })
            .fold(f64::INFINITY, f64::min)
    };
    let verified = time(&|| {
        let mut out = [0u8; 20];
        pbkdf2_hmac::<Sha1>(pw, salt, NonZeroU32::new(n).unwrap(), &mut out);
        std::hint::black_box(out);
    });
    println!("{:16} {:8.1} ns/iteration", "verified", verified * 1e9 / f64::from(n));
    for (name, f) in variants {
        let s = time(&|| {
            std::hint::black_box(run(f, pw, salt, n - 1));
        });
        println!(
            "{name:16} {:8.1} ns/iteration  {:+6.1}%",
            s * 1e9 / f64::from(n),
            (s / verified - 1.0) * 100.0
        );
    }
}
