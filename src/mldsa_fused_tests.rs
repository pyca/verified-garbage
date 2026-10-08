//! Regression coverage for the internal signed fused arithmetic boundary.
use crate::arch::mldsa::{vg_mldsa_inv_ntt, vg_mldsa_multiply_inverse_raw, vg_mldsa_multiply_ntt};

const Q: u32 = 8_380_417;
const SENTINEL: u64 = 0x9f38_a427_56d0_be13;

#[repr(C)]
struct GuardedPoly {
    before: [u64; 2],
    coefficients: [u32; 256],
    after: [u64; 2],
}

impl GuardedPoly {
    fn new(coefficients: [u32; 256]) -> Self {
        Self {
            before: [SENTINEL; 2],
            coefficients,
            after: [SENTINEL; 2],
        }
    }

    fn check_guards(&self) {
        assert_eq!(self.before, [SENTINEL; 2]);
        assert_eq!(self.after, [SENTINEL; 2]);
    }
}

#[repr(C)]
struct GuardedScratch {
    before: [u64; 2],
    words: [u64; 128],
    after: [u64; 2],
}

#[test]
fn raw_multiply_inverse_matches_canonical_composition() {
    let mut random = 0x358c_193a_ef02_72d1u64;
    for case in 0..80 {
        let mut coefficient = |i: usize, offset: usize| {
            const EDGES: [u32; 7] = [0, 1, Q - 1, Q, 2 * Q - 1, 2 * Q, 3 * Q - 1];
            if case < EDGES.len() {
                EDGES[(case + offset) % EDGES.len()]
            } else if case == EDGES.len() {
                EDGES[(i + offset) % EDGES.len()]
            } else {
                random ^= random << 13;
                random ^= random >> 7;
                random ^= random << 17;
                (random % u64::from(3 * Q)) as u32
            }
        };
        let a = GuardedPoly::new(core::array::from_fn(|i| coefficient(i, 0)));
        let b = GuardedPoly::new(core::array::from_fn(|i| coefficient(i, 3)));
        let canonical_a = a.coefficients.map(|x| x % Q);
        let canonical_b = b.coefficients.map(|x| x % Q);
        let original_a = a.coefficients;
        let original_b = b.coefficients;
        let mut reference = [0u32; 256];
        let mut reference_scratch = [0u64; 128];
        let mut output = GuardedPoly::new([u32::MAX; 256]);
        let mut scratch = GuardedScratch {
            before: [SENTINEL; 2],
            words: [SENTINEL; 128],
            after: [SENTINEL; 2],
        };
        // SAFETY: inputs obey their respective bounds, all buffers have the
        // generated sizes, and writable buffers are disjoint from inputs.
        unsafe {
            vg_mldsa_multiply_ntt(&mut reference, &canonical_a, &canonical_b);
            vg_mldsa_inv_ntt(&mut reference, &mut reference_scratch);
            vg_mldsa_multiply_inverse_raw(
                &mut output.coefficients,
                &a.coefficients,
                &b.coefficients,
                &mut scratch.words,
            );
        }
        for (actual, expected) in output.coefficients.into_iter().zip(reference) {
            let signed = i64::from(actual as i32);
            assert!(signed > -i64::from(Q) && signed < 2 * i64::from(Q));
            assert_eq!(signed.rem_euclid(i64::from(Q)) as u32, expected);
        }
        assert_eq!(a.coefficients, original_a);
        assert_eq!(b.coefficients, original_b);
        a.check_guards();
        b.check_guards();
        output.check_guards();
        assert_eq!(scratch.before, [SENTINEL; 2]);
        assert_eq!(scratch.after, [SENTINEL; 2]);
    }
}

#[test]
fn canonicalize_signed_matches_modular_reference() {
    use crate::arch::mldsa::vg_mldsa_canonicalize_signed;

    const EDGES: [i32; 9] = [
        -(Q as i32) + 1,
        -524_287,
        -131_071,
        -1,
        0,
        1,
        131_071,
        524_287,
        Q as i32 - 1,
    ];
    let mut random = 0xb6e3_12f9_4c70_a85du64;
    for case in 0..80 {
        let coefficients = core::array::from_fn(|i| {
            let signed = if case < EDGES.len() {
                EDGES[(i + case) % EDGES.len()]
            } else {
                random ^= random << 13;
                random ^= random >> 7;
                random ^= random << 17;
                (random % (2 * u64::from(Q) - 1)) as i32 - (Q as i32 - 1)
            };
            signed as u32
        });
        let expected = coefficients.map(|x| (x as i32).rem_euclid(Q as i32) as u32);
        let mut output = GuardedPoly::new(coefficients);
        // SAFETY: every signed coefficient lies strictly between -q and q;
        // the writable buffer contains exactly 256 coefficients.
        unsafe { vg_mldsa_canonicalize_signed(&mut output.coefficients) };
        assert_eq!(output.coefficients, expected);
        output.check_guards();
    }
}

fn next_random(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn canonical_signed(word: u32) -> u32 {
    (word as i32).rem_euclid(Q as i32) as u32
}

#[test]
fn signed_add_norm_matches_canonical_composition() {
    use crate::arch::mldsa::{vg_mldsa_add, vg_mldsa_norm_lt, vg_mldsa_signed_add_norm};

    let mut random = 0x0d84_f623_983a_17ceu64;
    for bound in [1u32, 2, 95_232 - 78, 131_072 - 78, 261_888 - 196, 524_288] {
        let mut accepted = 0;
        let mut rejected = 0;
        for case in 0..80 {
            let y = core::array::from_fn(|i| match case {
                0..=5 => [0, 1, Q - 1, Q - 2, Q / 2, Q / 2 + 1][case],
                _ => (next_random(&mut random) % u64::from(Q) + i as u64) as u32 % Q,
            });
            let raw = core::array::from_fn(|i| {
                if case < 12 {
                    let edges = [
                        -(Q as i32) + 1,
                        -1,
                        0,
                        1,
                        Q as i32 - 1,
                        Q as i32,
                        2 * Q as i32 - 1,
                    ];
                    edges[(case + i) % edges.len()] as u32
                } else if case < 32 {
                    // Force accepted and exact-boundary rejected polynomials,
                    // including rejection in each SIMD lane and the last group.
                    let target = match case % 5 {
                        0 => 0,
                        1 => bound as i32 - 1,
                        2 => -(bound as i32) + 1,
                        3 if i == 255 => bound as i32,
                        4 if i == case % 4 => -(bound as i32),
                        _ => 0,
                    };
                    let canonical = (target - y[i] as i32).rem_euclid(Q as i32);
                    (canonical
                        + match (i + case) % 3 {
                            0 if canonical != 0 => -(Q as i32),
                            1 => Q as i32,
                            _ => 0,
                        }) as u32
                } else {
                    ((next_random(&mut random) % (3 * u64::from(Q) - 1)) as i32 - (Q as i32 - 1))
                        as u32
                }
            });
            let input = GuardedPoly::new(raw);
            let mut output = GuardedPoly::new(y);
            let mut reference = y;
            let reference_input = raw.map(canonical_signed);
            // SAFETY: canonical reference inputs are reduced; raw input lies
            // strictly in (-q, 2q), the bound is valid, and buffers are disjoint.
            let (actual, expected) = unsafe {
                vg_mldsa_add(&mut reference, &reference_input);
                (
                    vg_mldsa_signed_add_norm(&mut output.coefficients, &input.coefficients, bound),
                    vg_mldsa_norm_lt(&reference, bound),
                )
            };
            assert_eq!(actual, expected, "bound={bound}, case={case}");
            if actual == 1 {
                accepted += 1;
            } else {
                rejected += 1;
            }
            for i in 0..256 {
                let signed = output.coefficients[i] as i32;
                assert!(signed > -(Q as i32) && signed < Q as i32);
                assert_eq!(canonical_signed(output.coefficients[i]), reference[i]);
                if actual == 1 {
                    assert!(signed.unsigned_abs() < bound);
                }
            }
            assert_eq!(input.coefficients, raw);
            input.check_guards();
            output.check_guards();
        }
        assert!(accepted > 0 && rejected > 0);
    }
}

#[test]
fn signed_sub_low_norm_matches_canonical_composition() {
    use crate::arch::mldsa::{
        vg_mldsa_high_bits, vg_mldsa_low_bits, vg_mldsa_norm_lt, vg_mldsa_signed_sub_low_norm,
        vg_mldsa_sub,
    };

    let mut random = 0x728b_40e5_a9c3_6d1fu64;
    for gamma in [95_232u32, 261_888] {
        for bound in [1u32, 2, gamma - 196, gamma, 524_288] {
            let mut accepted = 0;
            let mut rejected = 0;
            for case in 0..80 {
                let w = core::array::from_fn(|_| (next_random(&mut random) % u64::from(Q)) as u32);
                let raw = core::array::from_fn(|i| {
                    if case < 8 {
                        [
                            -(Q as i32) + 1,
                            -1,
                            0,
                            1,
                            Q as i32 - 1,
                            Q as i32,
                            2 * Q as i32 - 1,
                        ][(case + i) % 7] as u32
                    } else if case < 40 {
                        let targets = [
                            0,
                            1,
                            Q - 1,
                            gamma,
                            gamma + 1,
                            Q - gamma,
                            Q - gamma - 1,
                            2 * gamma,
                            2 * gamma - 1,
                            2 * gamma + 1,
                        ];
                        let target = if case < 18 {
                            targets[case - 8] % Q
                        } else if case < 30 {
                            targets[i % targets.len()]
                        } else if i == 255 {
                            bound.min(gamma)
                        } else {
                            0
                        };
                        let canonical = (w[i] as i32 - target as i32).rem_euclid(Q as i32);
                        (canonical
                            + match (i + case) % 3 {
                                0 if canonical != 0 => -(Q as i32),
                                1 => Q as i32,
                                _ => 0,
                            }) as u32
                    } else {
                        ((next_random(&mut random) % (3 * u64::from(Q) - 1)) as i32
                            - (Q as i32 - 1)) as u32
                    }
                });
                let input = GuardedPoly::new(raw);
                let mut high = GuardedPoly::new(w);
                let mut low = GuardedPoly::new([u32::MAX; 256]);
                let mut reference = w;
                let canonical = raw.map(canonical_signed);
                let mut expected_high = [0u32; 256];
                let mut expected_low = [0u32; 256];
                // SAFETY: the raw and canonical inputs satisfy their respective
                // bounds; both outputs and the input are disjoint full arrays.
                let (actual, expected) = unsafe {
                    vg_mldsa_sub(&mut reference, &canonical);
                    vg_mldsa_high_bits(&reference, gamma, &mut expected_high);
                    vg_mldsa_low_bits(&reference, gamma, &mut expected_low);
                    (
                        vg_mldsa_signed_sub_low_norm(
                            &mut high.coefficients,
                            &input.coefficients,
                            &mut low.coefficients,
                            gamma,
                            bound,
                        ),
                        vg_mldsa_norm_lt(&expected_low, bound),
                    )
                };
                assert_eq!(
                    actual, expected,
                    "gamma={gamma}, bound={bound}, case={case}"
                );
                assert_eq!(high.coefficients, expected_high);
                assert_eq!(low.coefficients.map(canonical_signed), expected_low);
                for value in low.coefficients {
                    let signed = value as i32;
                    assert!(signed >= -(gamma as i32) && signed <= gamma as i32);
                }
                if actual == 1 {
                    accepted += 1;
                } else {
                    rejected += 1;
                }
                assert_eq!(input.coefficients, raw);
                input.check_guards();
                high.check_guards();
                low.check_guards();
            }
            assert!(accepted > 0);
            if bound <= gamma {
                assert!(rejected > 0);
            }
        }
    }
}

#[test]
fn signed_hint_norm_matches_canonical_composition() {
    use crate::arch::mldsa::{
        vg_mldsa_add, vg_mldsa_high_bits, vg_mldsa_low_bits, vg_mldsa_make_hint, vg_mldsa_norm_lt,
        vg_mldsa_signed_hint_norm,
    };

    let mut random = 0xf721_5d83_ac06_b49eu64;
    for gamma in [95_232u32, 261_888] {
        let mut accepted = 0;
        let mut rejected = 0;
        let mut hints_seen = 0;
        for case in 0..80 {
            let base = core::array::from_fn(|i| {
                if case < 20 {
                    [
                        0,
                        1,
                        Q - 1,
                        gamma,
                        gamma + 1,
                        Q - gamma,
                        Q - gamma - 1,
                        2 * gamma - 1,
                        2 * gamma,
                        2 * gamma + 1,
                    ][(i + case) % 10]
                } else {
                    (next_random(&mut random) % u64::from(Q)) as u32
                }
            });
            let raw = core::array::from_fn(|i| {
                if case < 16 {
                    let value = [
                        0,
                        1,
                        -1,
                        gamma as i32 - 1,
                        -(gamma as i32) + 1,
                        gamma as i32,
                        -(gamma as i32),
                        Q as i32 - 1,
                    ][case % 8];
                    (value
                        + if case < 8 {
                            0
                        } else if value < 0 {
                            Q as i32
                        } else {
                            0
                        }) as u32
                } else if case < 24 {
                    [
                        -(Q as i32) + 1,
                        2 * Q as i32 - 1,
                        Q as i32,
                        gamma as i32,
                        -(gamma as i32),
                    ][i % 5] as u32
                } else {
                    ((next_random(&mut random) % (3 * u64::from(Q) - 1)) as i32 - (Q as i32 - 1))
                        as u32
                }
            });
            let ct = GuardedPoly::new(raw);
            let canonical_ct = raw.map(canonical_signed);
            let negative_ct = canonical_ct.map(|v| if v == 0 { 0 } else { Q - v });
            let mut high = GuardedPoly::new([0; 256]);
            let mut low = GuardedPoly::new([0; 256]);
            let mut canonical_low = [0u32; 256];
            let mut sum = base;
            let mut expected_hints = [0u32; 256];
            // SAFETY: all reference inputs are canonical, raw ct0 lies in
            // (-q,2q), and low/high are the exact decomposition of base.
            let (actual, expected) = unsafe {
                vg_mldsa_high_bits(&base, gamma, &mut high.coefficients);
                vg_mldsa_low_bits(&base, gamma, &mut canonical_low);
                low.coefficients = canonical_low.map(|v| {
                    if v > Q / 2 {
                        (v as i32 - Q as i32) as u32
                    } else {
                        v
                    }
                });
                vg_mldsa_add(&mut sum, &canonical_ct);
                let count = vg_mldsa_make_hint(&negative_ct, &sum, gamma, &mut expected_hints);
                let valid = vg_mldsa_norm_lt(&canonical_ct, gamma);
                (
                    vg_mldsa_signed_hint_norm(
                        &mut low.coefficients,
                        &ct.coefficients,
                        &high.coefficients,
                        gamma,
                    ),
                    u64::from(count) | (u64::from(valid) << 32),
                )
            };
            assert_eq!(actual, expected, "gamma={gamma}, case={case}");
            assert_eq!(low.coefficients, expected_hints);
            assert_eq!(ct.coefficients, raw);
            let mut expected_high = [0u32; 256];
            // SAFETY: base is canonical and the output is a disjoint full array.
            unsafe { vg_mldsa_high_bits(&base, gamma, &mut expected_high) };
            assert_eq!(high.coefficients, expected_high);
            hints_seen += actual as u32;
            if actual >> 32 == 1 {
                accepted += 1;
            } else {
                rejected += 1;
            }
            ct.check_guards();
            high.check_guards();
            low.check_guards();
        }
        assert!(accepted > 0 && rejected > 0 && hints_seen > 0);
    }
}
