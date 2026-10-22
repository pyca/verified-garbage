//! Investigation only: compare existing, verified kernels at P521's width.
//! This measures their current ABIs with initialized, warm workspaces. It
//! excludes a future adapter and does not measure ECDSA/ECDH end to end.
#![allow(dead_code)]

#[cfg(not(target_arch = "arm"))]
compile_error!("build for armv7-unknown-linux-gnueabihf");

#[path = "../../src/cpu.rs"]
mod cpu;
#[path = "../../src/asm/arm/p521_mont.rs"]
mod p521;
#[path = "../../src/asm/arm/rsa_mont.rs"]
mod rsa;

use std::hint::black_box;
use std::time::Instant;

type Current = unsafe extern "C" fn(*mut [u64; 1024], u32, u32, u32);

#[derive(Clone, Copy, Debug)]
enum Kernel {
    Current,
    RsaBase,
    RsaUmaal,
}

struct Workspace {
    current: [u64; 1024],
    rsa: [u64; 120],
    mul: Current,
}

impl Workspace {
    fn new(mul: Current) -> Self {
        Self {
            current: [0; 1024],
            rsa: [0; 120],
            mul,
        }
    }

    fn modulus(&mut self) -> [u64; 9] {
        // Obtain the domain parameter from the existing Lean-emitted code.
        // SAFETY: full workspace, zero canonical operands, disjoint result.
        unsafe { (self.mul)(&raw mut self.current, 144, 0, 72) };
        self.current[486..495].try_into().unwrap()
    }

    fn prepare(&mut self, modulus: &[u64; 9], a: &[u64; 9], b: &[u64; 9]) {
        self.current[..9].copy_from_slice(a);
        self.current[9..18].copy_from_slice(b);
        self.rsa[6] = 9;
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(modulus[0].wrapping_mul(inv)));
        }
        self.rsa[7] = inv.wrapping_neg();
        for j in 0..8 {
            self.rsa[8 + j] = self.rsa.as_ptr().wrapping_add(32 + j * 11) as usize as u64;
        }
        self.rsa[32..41].copy_from_slice(modulus);
        self.rsa[43..52].copy_from_slice(a);
        self.rsa[76..85].copy_from_slice(b);
    }

    fn call(&mut self, kernel: Kernel, alias: usize) {
        // SAFETY: prepare initializes the complete RSA layout (w=9), odd
        // modulus and inverse, canonical b, and valid public indices. Both
        // buffers are separate from the call stack and have the required
        // sizes. The UMAAL caller checks the emitted feature requirement.
        unsafe {
            match kernel {
                Kernel::Current => {
                    (self.mul)(black_box(&raw mut self.current), [144, 0, 72][alias], 0, 72)
                }
                Kernel::RsaBase => rsa::vg_rsa_mont_mul(
                    black_box(self.rsa.as_mut_ptr()),
                    120,
                    [5, 1, 4][alias],
                    1,
                    4,
                ),
                Kernel::RsaUmaal => rsa::vg_rsa_mont_mul_umaal(
                    black_box(self.rsa.as_mut_ptr()),
                    120,
                    [5, 1, 4][alias],
                    1,
                    4,
                ),
            }
        }
    }

    fn output(&self, kernel: Kernel, alias: usize) -> [u64; 9] {
        let (buffer, start) = match kernel {
            Kernel::Current => (&self.current[..], [18, 0, 9][alias]),
            _ => (&self.rsa[..], 32 + [5, 1, 4][alias] * 11),
        };
        buffer[start..start + 9].try_into().unwrap()
    }

    fn measure(&mut self, kernel: Kernel, iterations: usize) -> f64 {
        for _ in 0..2000 {
            self.call(kernel, 0);
        }
        let start = Instant::now();
        for _ in 0..iterations {
            self.call(kernel, 0);
        }
        let elapsed = start.elapsed().as_nanos() as f64 / iterations as f64;
        black_box(self.output(kernel, 0));
        elapsed
    }
}

fn below(mut n: [u64; 9], amount: u64) -> [u64; 9] {
    let (v, mut borrow) = n[0].overflowing_sub(amount);
    n[0] = v;
    for x in &mut n[1..] {
        let (v, b) = x.overflowing_sub(u64::from(borrow));
        *x = v;
        borrow = b;
    }
    assert!(!borrow);
    n
}

fn random(seed: &mut u64) -> [u64; 9] {
    std::array::from_fn(|_| {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        *seed
    })
}

fn main() {
    assert!(cpu::detected().contains(rsa::VG_RSA_MONT_MUL_UMAAL_FEATURES));
    let kernels = [Kernel::Current, Kernel::RsaBase, Kernel::RsaUmaal];
    for (mod_name, mul) in [
        ("p", p521::vg_p521_mul_mod_p as Current),
        ("n", p521::vg_p521_mul_mod_n as Current),
    ] {
        let mut ws = Workspace::new(mul);
        let modulus = ws.modulus();
        let mut seed = 521u64;
        let mut cases = vec![
            ([0; 9], [0; 9]),
            (below(modulus, 1), below(modulus, 2)),
            ([u64::MAX; 9], below(modulus, 1)),
        ];
        for bit in 0..576 {
            let mut a = [0; 9];
            a[bit / 64] = 1 << (bit % 64);
            cases.push((a, below(modulus, 1)));
        }
        for _ in 0..1024 {
            let a = random(&mut seed);
            let mut b = random(&mut seed);
            b[8] = 0; // Below 2^512, hence below either 521-bit modulus.
            cases.push((a, b));
        }
        for (a, b) in &cases {
            ws.prepare(&modulus, a, b);
            ws.call(Kernel::Current, 0);
            let expected = ws.output(Kernel::Current, 0);
            for kernel in kernels {
                for alias in 0..3 {
                    ws.prepare(&modulus, a, b);
                    ws.call(kernel, alias);
                    assert_eq!(
                        ws.output(kernel, alias),
                        expected,
                        "{mod_name}/{kernel:?}/{alias}"
                    );
                }
            }
        }
        println!(
            "correctness: {mod_name}, {} cases, three kernels, three output aliases",
            cases.len()
        );
        let timed = [
            ("dense", cases[579]),
            ("near_modulus", cases[1]),
            ("full_width_a", cases[2]),
        ];
        for (case_name, (a, b)) in timed {
            let mut samples: [Vec<f64>; 3] = std::array::from_fn(|_| Vec::new());
            for round in 0..11 {
                for k in 0..3 {
                    let index = (k + round) % 3;
                    ws.prepare(&modulus, &a, &b);
                    let ns = ws.measure(kernels[index], 100_000);
                    samples[index].push(ns);
                    println!(
                        "{{\"kind\":\"sample\",\"modulus\":\"{mod_name}\",\"case\":\"{case_name}\",\"kernel\":\"{:?}\",\"round\":{round},\"ns\":{ns:.3}}}",
                        kernels[index]
                    );
                }
            }
            for (kernel, mut sample) in kernels.into_iter().zip(samples) {
                sample.sort_by(f64::total_cmp);
                println!(
                    "{{\"kind\":\"summary\",\"modulus\":\"{mod_name}\",\"case\":\"{case_name}\",\"kernel\":\"{kernel:?}\",\"samples\":11,\"min_ns\":{:.3},\"median_ns\":{:.3},\"max_ns\":{:.3}}}",
                    sample[0], sample[5], sample[10]
                );
            }
        }
    }
}
