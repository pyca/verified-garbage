use super::{Error, Parameters, Vec};
use crate::dsa::PrivateKey;
use crate::dsa::tests::vectors::hex;

struct Vector {
    bits: usize,
    p: Vec<u8>,
    q: Vec<u8>,
    seed: Vec<u8>,
}

fn prime_vectors() -> Vec<Vector> {
    let mut section = "";
    let mut mode = "";
    let mut p = "";
    let mut q = "";
    let mut seed = "";
    let mut cases = Vec::new();
    for line in include_str!("../../../vectors/nist-cavp-dsa/PQGGen.txt").lines() {
        if line.starts_with("[A.") {
            section = line;
        } else if line.starts_with("[mod = ") {
            mode = line;
        } else if section.starts_with("[A.1.1.2 ") {
            // Indented P/counter lines are intermediate candidates, not
            // the published final answers.
            if let Some(value) = line.strip_prefix("P = ") {
                p = value;
            } else if let Some(value) = line.strip_prefix("Q = ") {
                q = value;
            } else if let Some(value) = line.strip_prefix("domain_parameter_seed = ") {
                seed = value;
            } else if line.starts_with("counter = ") {
                let bits = match mode {
                    "[mod = L=1024, N=160, SHA-1]" => 1024,
                    "[mod = L=2048, N=256, SHA-256]" => 2048,
                    "[mod = L=3072, N=256, SHA-256]" => 3072,
                    _ => continue,
                };
                if !cases.iter().any(|v: &Vector| v.bits == bits) {
                    cases.push(Vector {
                        bits,
                        p: hex(p, 0),
                        q: hex(q, 0),
                        seed: hex(seed, 0),
                    });
                }
            }
        }
    }
    assert_eq!(cases.len(), 3);
    cases
}

/// One refillable tape: the published seed, then 0x02 octets for its
/// witnesses and generator candidates (deterministic, for known answers;
/// production obtains independent bytes from the OS), and 0x02 octets in
/// any refill.
fn fill_known_answer(v: &Vector, tape: usize, buf: &mut [u8]) {
    buf.fill(2);
    if tape == 0 {
        buf[..v.seed.len()].copy_from_slice(&v.seed);
    }
}

const KNOWN_ANSWER_FILLS: usize = 1;

#[test]
fn cavp_generated_parameters() {
    for v in prime_vectors() {
        let mut tape = 0;
        let parameters = Parameters::generate_from(v.bits, |buf| {
            fill_known_answer(&v, tape, buf);
            tape += 1;
            Ok(())
        })
        .unwrap();
        assert!(tape >= KNOWN_ANSWER_FILLS);
        assert_eq!(parameters.p(), v.p);
        assert_eq!(parameters.q(), v.q);
        assert_eq!(parameters.g().len(), v.p.len());
        let key = PrivateKey::generate(parameters.p(), parameters.q(), parameters.g()).unwrap();
        let digest = [0x53; 32];
        let signature = key.sign(&digest).unwrap();
        assert!(key.public_key().verify(&digest, &signature).is_ok());
    }
}

const FILLS: usize = 2;

#[test]
fn parameter_generation_errors() {
    for bits in [0, 512, 2047, 4096] {
        assert_eq!(Parameters::generate(bits).unwrap_err(), Error::Length);
    }
    // The tape is filled, then refilled once before the 0x02 seeds below
    // exhaust the search.
    for fail_at in 0..FILLS {
        let mut fills = 0;
        let result = Parameters::generate_from(1024, |buf| {
            let fail = fills == fail_at;
            fills += 1;
            if fail {
                Err(Error::Randomness)
            } else {
                buf.fill(2);
                Ok(())
            }
        });
        assert_eq!(result.unwrap_err(), Error::Randomness);
        assert_eq!(fills, fail_at + 1);
    }
    // Repeated 0x02 seeds produce a subgroup candidate divisible by 3.
    // The verified search exhausts the seed tape and reports failure.
    assert_eq!(
        Parameters::generate_from(1024, |buf| {
            buf.fill(2);
            Ok(())
        })
        .unwrap_err(),
        Error::InvalidKeyOrNonce
    );
}

#[test]
fn generated_parameters_with_os_randomness() {
    let parameters = Parameters::generate(1024).unwrap();
    let key = PrivateKey::generate(parameters.p(), parameters.q(), parameters.g()).unwrap();
    let digest = [0x47; 20];
    assert!(
        key.public_key()
            .verify(&digest, &key.sign(&digest).unwrap())
            .is_ok()
    );
}
