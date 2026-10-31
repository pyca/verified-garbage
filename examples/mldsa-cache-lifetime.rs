// Measurement-only harness. Not a known-answer test or a production API.
use std::{hint::black_box, sync::Barrier, thread, time::Instant};
const MESSAGE: &[u8; 64] = &[0x42; 64];
fn median(mut xs: Vec<f64>) -> f64 {
    xs.sort_by(f64::total_cmp);
    (xs[(xs.len() - 1) / 2] + xs[xs.len() / 2]) / 2.0
}
macro_rules! measure {
    ($module:ident, $sk:ident, $vk:ident, $id:literal) => {{
        use verified_garbage::$module::{$sk, $vk};
        fn send_sync<T: Send + Sync>() {}
        send_sync::<$sk>();
        send_sync::<$vk>();
        // The same fixed 32-key workload in every policy binary. Fixtures and
        // their signatures are prepared before the timed key lifetimes.
        let fixtures: Vec<_> = (0..32u8)
            .map(|i| {
                let mut seed = [0u8; 32];
                verified_garbage::hashes::sha3::Shake256::digest(&[i, 0x83, 0x27], &mut seed);
                let key = $sk::from_seed(&seed).unwrap();
                let sig = key.sign_deterministic(MESSAGE, b"").unwrap();
                (seed, *key.verifying_key().as_bytes(), sig)
            })
            .collect();
        for operation in ["sign", "verify"] {
            for count in [1usize, 2, 4, 8, 16, 100] {
                let batch = 128usize.div_ceil(count);
                let mut samples = Vec::new();
                for sample in 0..16 {
                    let start = Instant::now();
                    for life in 0..batch {
                        let (seed, pk, sig) = &fixtures[(life + sample * 7) % fixtures.len()];
                        if operation == "sign" {
                            let key = $sk::from_seed(black_box(seed)).unwrap();
                            for _ in 0..count {
                                black_box(key.sign_deterministic(black_box(MESSAGE), b"").unwrap());
                            }
                            drop(black_box(key));
                        } else {
                            let key = $vk::from_bytes(black_box(pk));
                            for _ in 0..count {
                                black_box(key.verify(black_box(MESSAGE), b"", black_box(sig)))
                                    .unwrap();
                            }
                            drop(black_box(key));
                        }
                    }
                    samples.push(start.elapsed().as_secs_f64() * 1e6 / batch as f64);
                }
                println!(
                    "life,{},{},{},{:.6}",
                    $id,
                    operation,
                    count,
                    median(samples)
                );
            }
        }
        for operation in ["sign", "verify"] {
            for warm in [false, true] {
                let mut samples = Vec::new();
                for repeat in 0..12 {
                    let (seed, pk, sig) = &fixtures[repeat];
                    let signing = $sk::from_seed(seed).unwrap();
                    let verifying = $vk::from_bytes(pk);
                    if warm {
                        for _ in 0..4 {
                            if operation == "sign" {
                                black_box(signing.sign_deterministic(MESSAGE, b"").unwrap());
                            } else {
                                verifying.verify(MESSAGE, b"", sig).unwrap();
                            }
                        }
                    }
                    let start_gate = Barrier::new(5);
                    let finish_gate = Barrier::new(5);
                    let elapsed = thread::scope(|scope| {
                        for _ in 0..4 {
                            let (signing, verifying, start_gate, finish_gate) =
                                (&signing, &verifying, &start_gate, &finish_gate);
                            scope.spawn(move || {
                                start_gate.wait();
                                for _ in 0..32 {
                                    if operation == "sign" {
                                        black_box(
                                            signing.sign_deterministic(MESSAGE, b"").unwrap(),
                                        );
                                    } else {
                                        verifying.verify(MESSAGE, b"", sig).unwrap();
                                    }
                                }
                                finish_gate.wait();
                            });
                        }
                        let start = Instant::now();
                        start_gate.wait();
                        finish_gate.wait();
                        start.elapsed()
                    });
                    samples.push(elapsed.as_secs_f64() * 1e6 / 128.0);
                }
                println!(
                    "threads4,{},{},{},{:.6}",
                    $id,
                    operation,
                    if warm { "warm" } else { "cold" },
                    median(samples)
                );
            }
        }
        println!(
            "sizes,{},{},{}",
            $id,
            std::mem::size_of::<$sk>(),
            std::mem::size_of::<$vk>()
        );
    }};
}
fn main() {
    measure!(mldsa44, SigningKey44, VerifyingKey44, 44);
    measure!(mldsa65, SigningKey65, VerifyingKey65, 65);
    measure!(mldsa87, SigningKey87, VerifyingKey87, 87);
}
