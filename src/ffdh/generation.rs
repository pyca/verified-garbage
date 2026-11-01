//! Entropy-tape service and safe-prime parameter generation.
//! The whole parameter search runs in
//! verified code (`vg_ffdh_generate_parameters`): the candidates, their
//! Miller–Rabin witnesses, the attempt limit and the length of each entropy
//! request. Rust allocates, fills the random tape the controller asks for
//! and selects the implementation for the CPU.
use super::Error;
use super::Parameters;
use super::arithmetic::Backend;
#[cfg(not(any(target_arch = "arm", target_arch = "x86")))]
use crate::arch::ffdh::vg_ffdh_generate_parameters;
#[cfg(target_arch = "x86_64")]
use crate::arch::ffdh::vg_ffdh_generate_parameters_adx;
#[cfg(any(target_arch = "arm", target_arch = "x86"))]
use crate::arch::ffdh::vg_ffdh_generate_parameters_sieved as vg_ffdh_generate_parameters;
#[cfg(target_arch = "arm")]
use crate::arch::ffdh::vg_ffdh_generate_parameters_sieved_umaal as vg_ffdh_generate_parameters_umaal;
use crate::arch::ffdh::vg_ffdh_parameter_generation_init;
use crate::cpu::detected;
use crate::rsa::Scratch;
use crate::zeroize::zeroize;
use alloc::{vec, vec::Vec};

/// A random tape, wiped when dropped: a controller may keep secrets in it.
struct Tape(Vec<u8>);
impl Drop for Tape {
    fn drop(&mut self) {
        zeroize(&mut self.0);
    }
}

/// Run a verified controller to completion over a random tape of
/// `requested` bytes from `fill`. `step` runs it on the tape and returns
/// its status (1 done, 3 out of attempts, 0 for more entropy), the bytes
/// it consumed and its next request. For 0, the unconsumed rest of the
/// tape is kept and extended with fresh bytes to the request, as the
/// controllers' contracts say.
pub(super) fn serve<E>(
    requested: usize,
    mut fill: impl FnMut(&mut [u8]) -> Result<(), E>,
    mut step: impl FnMut(&[u8]) -> (u32, usize, usize),
) -> Result<(), Error> {
    let mut tape = Tape(vec![0; requested]);
    fill(&mut tape.0).map_err(|_| Error::Randomness)?;
    loop {
        let (status, used, requested) = step(&tape.0);
        match status {
            1 => return Ok(()),
            3 => return Err(Error::TooManyIterations),
            0 => {
                let rest = &tape.0[used..];
                let mut next = Tape(vec![0; requested]);
                next.0[..rest.len()].copy_from_slice(rest);
                fill(&mut next.0[rest.len()..]).map_err(|_| Error::Randomness)?;
                tape = next;
            }
            // The verified controllers return only 0, 1 or 3.
            // NO-COVERAGE-START
            _ => unreachable!(),
            // NO-COVERAGE-END
        }
    }
}

/// The parameter-generation controller's 16 words: the attempts left, the
/// width of p in bytes, the entropy cap and the next request, then private
/// working space (`vg_ffdh_parameter_generation_init`).
struct Controller(Scratch);
impl Controller {
    fn new(bits: usize, generator: u32) -> Result<Self, Error> {
        let mut state = Self(Scratch::new(16));
        // SAFETY: `state` is 16 writable words, a Rust object of its own.
        let ok = unsafe {
            vg_ffdh_parameter_generation_init(state.0.as_mut_ptr().cast(), bits, generator)
        };
        if ok == 1 {
            Ok(state)
        } else {
            Err(Error::InvalidParameters)
        }
    }

    /// Run the search on `tape` into `p`: the status, the bytes of the tape
    /// consumed and the next request (`vg_ffdh_generate_parameters`).
    fn search(
        &mut self,
        bits: usize,
        generator: u32,
        tape: &[u8],
        p: &mut [u8],
        ws: &mut Scratch,
    ) -> (u32, usize, usize) {
        assert!(p.len() == self.0[1] as usize && ws.len() >= 16 * p.len() + 32);
        assert!(tape.len() <= self.0[2] as usize);
        let f = match Backend::ffdh(detected()) {
            Backend::Baseline => vg_ffdh_generate_parameters,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_ffdh_generate_parameters_adx,
            #[cfg(target_arch = "arm")]
            Backend::Umaal => vg_ffdh_generate_parameters_umaal,
        };
        let mut used = [0u64; 1];
        // SAFETY: `self` was initialized for `bits` and `generator` and has
        // only been passed to this function since, which keeps its words
        // as the contract's precondition needs; `p` is its width, `ws` at
        // least `16 * p.len() + 32` words and the tape at most its cap. All
        // are distinct Rust objects. A variant is selected only when the CPU
        // has its generated feature set.
        let status = unsafe {
            f(
                p.as_mut_ptr(),
                p.len(),
                &mut used,
                bits,
                generator,
                tape.as_ptr(),
                tape.len(),
                ws.as_mut_ptr(),
                ws.len(),
                self.0.as_mut_ptr().cast(),
            )
        };
        (status, used[0] as usize, self.0[3] as usize)
    }
}

pub(super) fn parameters<E>(
    size: usize,
    generator: u32,
    fill: impl FnMut(&mut [u8]) -> Result<(), E>,
) -> Result<Parameters, Error> {
    search(size, generator, Controller::new(size, generator)?, fill)
}

fn search<E>(
    size: usize,
    generator: u32,
    mut state: Controller,
    fill: impl FnMut(&mut [u8]) -> Result<(), E>,
) -> Result<Parameters, Error> {
    let len = state.0[1] as usize;
    let mut p = vec![0; len];
    let mut ws = Scratch::new(16 * len + 32);
    serve(state.0[3] as usize, fill, |tape| {
        state.search(size, generator, tape, &mut p, &mut ws)
    })?;
    Parameters::from_components(&p, &generator.to_be_bytes(), None)
}

/// `parameters` with at most `limit` candidates.
#[cfg(test)]
fn parameters_limit<E>(
    size: usize,
    generator: u32,
    limit: usize,
    fill: impl FnMut(&mut [u8]) -> Result<(), E>,
) -> Result<Parameters, Error> {
    let mut state = Controller::new(size, generator)?;
    state.0[0] = state.0[0].min(limit as u64);
    search(size, generator, state, fill)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parameter_failure_is_bounded() {
        assert_eq!(
            parameters_limit(512, 2, 1, |_| Err(())).unwrap_err(),
            Error::Randomness
        );
        assert_eq!(
            parameters_limit(512, 2, 1, |out| {
                out.fill(0);
                Ok::<_, ()>(())
            })
            .unwrap_err(),
            Error::TooManyIterations
        );
        assert_eq!(
            parameters_limit(512, 5, 1, |out| {
                out.fill(0);
                Ok::<_, ()>(())
            })
            .unwrap_err(),
            Error::TooManyIterations
        );
        assert_eq!(
            parameters_limit(511, 2, 1, |_| Ok::<_, ()>(())).unwrap_err(),
            Error::InvalidParameters
        );
    }

    /// A published safe prime of `bits` bits, from pyca/cryptography's
    /// vectors: `dhkey.txt` for 1024 bits, RFC 3526's groups above.
    fn published_prime(bits: usize) -> Vec<u8> {
        let text = if bits == 1024 {
            include_str!("../../vectors/cryptography-ffdh/dhkey/dhkey.txt")
        } else {
            include_str!("../../vectors/cryptography-ffdh/rfc3526/rfc3526.txt")
        };
        text.lines()
            .filter_map(|line| line.strip_prefix("P = "))
            .map(|hex| {
                let hex = hex.trim_start_matches('0');
                hex.as_bytes()
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|pair| {
                        u8::from_str_radix(core::str::from_utf8(pair).unwrap(), 16).unwrap()
                    })
                    .collect::<Vec<_>>()
            })
            .find(|p| p.len() * 8 == bits)
            .unwrap()
    }

    /// A tape whose first candidate is `prime`, followed by the witnesses
    /// for q and then p: n − 1 and n (out of range, at the width of n), 0
    /// and 1 (out of range), then `rounds` witnesses 2. The number of bytes
    /// the candidate consumes.
    fn candidate_tape(prime: &[u8], rounds: usize) -> (Vec<u8>, usize) {
        let len = prime.len();
        let mut tape = prime.to_vec();
        let mut carry = 0;
        let q: Vec<u8> = prime
            .iter()
            .map(|&b| {
                let half = (b >> 1) | carry;
                carry = b << 7;
                half
            })
            .collect();
        // The sieved candidate (ARMv7, x86) draws one witness for p first.
        #[cfg(any(target_arch = "arm", target_arch = "x86"))]
        let phases = [
            (prime.to_vec(), 1),
            (q, rounds),
            (prime.to_vec(), rounds - 1),
        ];
        #[cfg(not(any(target_arch = "arm", target_arch = "x86")))]
        let phases = [(q, rounds), (prime.to_vec(), rounds)];
        for (modulus, rounds) in phases {
            let mut upper = modulus.clone();
            *upper.last_mut().unwrap() -= 1;
            tape.extend_from_slice(&upper);
            tape.extend_from_slice(&modulus);
            for value in [0, 1].into_iter().chain(core::iter::repeat_n(2, rounds)) {
                tape.resize(tape.len() + len, 0);
                *tape.last_mut().unwrap() = value;
            }
        }
        let used = tape.len();
        (tape, used)
    }

    #[test]
    fn published_candidates_and_tape_consumption() {
        // Published safe primes exercise both 64- and 128-witness policies.
        // Zero, one, n − 1 and n are skipped independently in every phase.
        for (bits, generator, rounds) in [(1024, 2, 64), (3072, 5, 128)] {
            let prime = published_prime(bits);
            let len = prime.len();
            let (mut tape, used) = candidate_tape(&prime, rounds);
            tape.extend_from_slice(&[0xff; 17]);
            let mut ws = Scratch::new(16 * len + 32);
            let mut p = vec![0xaa; len];
            let mut state = Controller::new(bits, generator).unwrap();
            let attempts = state.0[0];
            assert_eq!(
                state.0[1..4],
                [len as u64, 32769 * len as u64, 512 * len as u64]
            );
            assert_eq!(
                state.search(bits, generator, &tape, &mut p, &mut ws),
                (1, used, 0)
            );
            assert_eq!(p, prime);
            assert_eq!(state.0[0], 0);
            // A tape that ends inside the candidate requests more entropy
            // and consumes nothing: twice the larger of the bytes left and
            // 256 per byte of p.
            // Exercise a late witness shortage at 1024 bits. The 3072-bit
            // success above covers the full 128-witness policy without
            // repeating almost all those rounds under ARM emulation.
            let late_cut = (bits == 1024).then_some(used - 1);
            for cut in [0, len - 1, len].into_iter().chain(late_cut) {
                let mut state = Controller::new(bits, generator).unwrap();
                assert_eq!(
                    state.search(bits, generator, &tape[..cut], &mut p, &mut ws),
                    (0, 0, 2 * cut.max(256 * len))
                );
                assert!(p.iter().all(|&b| b == 0));
                assert_eq!(state.0[0], attempts);
            }
        }
    }

    #[test]
    fn full_width_attempt_counter_and_request_words() {
        // The maximum-size policy starts at 2^32 attempts, a budget whose
        // low 32 bits are zero.
        let bits = 8192;
        let len = bits / 8;
        let mut state = Controller::new(bits, 2).unwrap();
        assert_eq!(state.0[0], 1u64 << 32);
        let mut p = vec![0xaa; len];
        let mut ws = Scratch::new(16 * len + 32);
        state.0[3] = u64::MAX;
        // 2^8192 - 1 fails the generator congruence: the search goes on to
        // an entropy request.
        assert_eq!(
            state.search(bits, 2, &vec![0xff; len], &mut p, &mut ws),
            (0, len, 512 * len)
        );
        assert_eq!(state.0[0], (1u64 << 32) - 1);
        assert_eq!(state.0[3], (512 * len) as u64);
        assert!(p.iter().all(|&b| b == 0));
        state.0[0] = 0;
        state.0[3] = u64::MAX;
        p.fill(0xaa);
        assert_eq!(state.search(bits, 2, &[], &mut p, &mut ws), (3, 0, 0));
        assert_eq!(state.0[3], 0);
        assert!(p.iter().all(|&b| b == 0));
    }

    #[test]
    fn rejected_candidates_are_consumed() {
        // Two candidates rejected by the generator's congruence (2^1024 − 1
        // is 15 mod 24, not 11), then the prime: the search continues
        // without returning, and consumes all three.
        let prime = published_prime(1024);
        let len = prime.len();
        let (candidate, used) = candidate_tape(&prime, 64);
        let mut tape = vec![0xff; 2 * len];
        tape.extend_from_slice(&candidate);
        let mut ws = Scratch::new(16 * len + 32);
        let mut p = vec![0; len];
        let mut state = Controller::new(1024, 2).unwrap();
        assert_eq!(
            state.search(1024, 2, &tape, &mut p, &mut ws),
            (1, 2 * len + used, 0)
        );
        assert_eq!(p, prime);
        // With one attempt left, the first rejection exhausts the search.
        let mut state = Controller::new(1024, 2).unwrap();
        state.0[0] = 1;
        assert_eq!(state.search(1024, 2, &tape, &mut p, &mut ws), (3, len, 0));
        assert!(p.iter().all(|&b| b == 0));
    }

    #[test]
    fn tape_extension_preserves_candidate_and_reports_rng_failure() {
        // The first tape holds the prime and no usable witness: the
        // controller asks for more, keeping the candidate, and finishes on
        // the extension's witnesses 2.
        let prime = published_prime(1024);
        let len = prime.len();
        let mut calls = 0;
        let params = parameters_limit(1024, 2, 1, |out| {
            calls += 1;
            out.fill(0);
            if calls == 1 {
                out[..len].copy_from_slice(&prime);
            } else {
                for draw in out.chunks_exact_mut(len) {
                    *draw.last_mut().unwrap() = 2;
                }
            }
            Ok::<_, ()>(())
        })
        .unwrap();
        assert_eq!(params.components().0, prime);
        assert_eq!(calls, 2);
        let mut calls = 0;
        assert_eq!(
            parameters_limit(1024, 2, 1, |out| {
                calls += 1;
                if calls == 1 {
                    out[..len].copy_from_slice(&prime);
                    Ok(())
                } else {
                    Err(())
                }
            })
            .unwrap_err(),
            Error::Randomness
        );
    }

    #[test]
    fn exhausted_entropy_cap() {
        // A candidate whose witnesses are all out of range keeps asking for
        // more until its tape reaches the entropy cap, then gives up.
        let prime = published_prime(1024);
        let mut calls = 0;
        assert_eq!(
            parameters_limit(1024, 2, 1, |out| {
                calls += 1;
                out.fill(0);
                if calls == 1 {
                    out[..prime.len()].copy_from_slice(&prime);
                }
                Ok::<_, ()>(())
            })
            .unwrap_err(),
            Error::TooManyIterations
        );
    }

    #[test]
    fn composite_q_at_modulus_width_boundaries() {
        // p with q = (p − 1) / 2 divisible by seven, while p passes the
        // generator's congruence and has no small prime factor, at widths
        // on both sides of a 64-bit word boundary.
        for bits in [512_usize, 513, 2049, 8192] {
            let len = bits.div_ceil(8);
            let mut candidate = vec![0; len];
            candidate[0] = 1 << ((bits - 1) % 8);
            let rem = |p: &[u8], d: u32| p.iter().fold(0, |r, &b| (256 * r + u32::from(b)) % d);
            let small_primes: Vec<u32> = (3..=251)
                .step_by(2)
                .filter(|&d| (3..d).step_by(2).all(|s| d % s != 0))
                .collect();
            let offset = (1u32..65536)
                .step_by(2)
                .find(|&offset| {
                    candidate[len - 2..].copy_from_slice(&(offset as u16).to_be_bytes());
                    rem(&candidate, 24) == 11
                        && rem(&candidate, 14) == 1
                        && small_primes.iter().all(|&d| rem(&candidate, d) != 0)
                })
                .unwrap();
            candidate[len - 2..].copy_from_slice(&(offset as u16).to_be_bytes());
            let mut p = vec![0xaa; len];
            let mut ws = Scratch::new(16 * len + 32);
            let mut state = Controller::new(bits, 2).unwrap();
            state.0[0] = 1;
            assert_eq!(
                state.search(bits, 2, &candidate, &mut p, &mut ws),
                (3, len, 0)
            );
            assert!(p.iter().all(|&b| b == 0));
        }
    }
}
