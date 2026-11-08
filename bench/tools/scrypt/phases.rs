//! Isolated allocation, derivation, wipe, free, and public-API timings.
//! Usage: phases N R P SAMPLES; SCRYPT_WIPE_MODE=chunks|bulk.

use std::{hint::black_box, sync::atomic, time::Instant};
use verified_garbage::kdf::scrypt::derive;
use verified_garbage_asm_x86_64::dispatch::{scrypt::vg_scrypt_auto, zeroize::vg_zeroize_auto};
#[derive(Clone)]
#[repr(C, align(64))]
struct Chunk([u8; 128]);
fn chunks(n: usize) -> Vec<Chunk> {
    let mut v = Vec::new();
    v.try_reserve_exact(n).unwrap();
    v.resize(n, Chunk([0; 128]));
    v
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 5, "usage: phases N R P SAMPLES");
    let n: usize = args[1].parse().unwrap();
    let r: usize = args[2].parse().unwrap();
    let p: usize = args[3].parse().unwrap();
    let reps: usize = args[4].parse().unwrap();
    assert!(n > 1 && n.is_power_of_two());
    assert!(r > 0 && u32::try_from(r).is_ok());
    assert!(p > 0 && u32::try_from(p).is_ok());
    assert!(r * 16 >= usize::BITS as usize || n < (1usize << (r * 16)));
    assert!(p as u128 <= u128::from(u32::MAX) * 32 / (128 * r as u128));
    assert!(reps > 0);
    let blen = r.checked_mul(p).unwrap();
    let vlen = r.checked_mul(n).unwrap();
    let bulk = std::env::var("SCRYPT_WIPE_MODE").as_deref() == Ok("bulk");
    for sample in 0..reps {
        let mut out = [0u8; 64];
        let start = Instant::now();
        let mut b = chunks(blen);
        let mut v = chunks(vlen);
        let mut s = chunks(r + 16);
        let alloc = start.elapsed().as_secs_f64();
        let start = Instant::now();
        // SAFETY: validated RFC parameters, separate writable aligned vectors,
        // read-only password/salt, and a separate 64-byte output. Rust allocations
        // cannot wrap or overlap the arguments/return address on the stack.
        unsafe {
            vg_scrypt_auto(
                b"password".as_ptr(),
                8,
                b"NaCl".as_ptr(),
                4,
                r,
                b.as_mut_ptr().cast(),
                blen,
                v.as_mut_ptr().cast(),
                vlen,
                s.as_mut_ptr().cast(),
                r + 16,
                out.as_mut_ptr(),
                64,
            )
        };
        let kernel = start.elapsed().as_secs_f64();
        black_box(&out);
        let start = Instant::now();
        // Match the corresponding destructor's call granularity. The fences
        // match zeroize_raw and do not generate machine instructions here.
        if bulk {
            for buf in [&mut b, &mut v, &mut s] {
                // SAFETY: the complete vector is writable; zero is valid for Chunk.
                unsafe {
                    vg_zeroize_auto(
                        buf.as_mut_ptr().cast(),
                        std::mem::size_of_val(buf.as_slice()),
                    )
                }
                atomic::compiler_fence(atomic::Ordering::SeqCst);
            }
        } else {
            for c in b.iter_mut().chain(v.iter_mut()).chain(s.iter_mut()) {
                // SAFETY: this chunk is writable for all 128 bytes.
                unsafe { vg_zeroize_auto(c.0.as_mut_ptr(), 128) }
                atomic::compiler_fence(atomic::Ordering::SeqCst);
            }
        }
        let wipe = start.elapsed().as_secs_f64();
        let start = Instant::now();
        drop((b, v, s));
        let free = start.elapsed().as_secs_f64();
        let start = Instant::now();
        let mut expected = [0u8; 64];
        derive(
            b"password",
            b"NaCl",
            n as u64,
            r as u32,
            p as u32,
            usize::MAX,
            &mut expected,
        )
        .unwrap();
        let full = start.elapsed().as_secs_f64();
        assert_eq!(out, expected);
        println!("{n},{r},{p},{sample},{alloc:.9},{kernel:.9},{wipe:.9},{free:.9},{full:.9}");
    }
}
