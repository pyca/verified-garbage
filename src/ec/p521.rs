//! P-521's multiplications, which [`ecdsa`](crate::ecdsa) and
//! [`ecdh`](crate::ecdh) choose between, and its public keys, which both
//! compute. On x86-64 CPUs with BMI2, ADX and AVX2, the `_adx` variants
//! multiply field elements with `mulx`, `adcx` and `adox`, and the
//! signatures' and public keys' comb selects its entries with AVX2.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use crate::arch::ec_p521::vg_ec_p521_public_key;
#[cfg(target_arch = "x86_64")]
use crate::arch::ec_p521::{VG_EC_P521_PUBLIC_KEY_ADX_FEATURES, vg_ec_p521_public_key_adx};
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdh_p521::VG_ECDH_P521_ADX_FEATURES;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p521::{VG_ECDSA_P521_SIGN_ADX_FEATURES, VG_ECDSA_P521_VERIFY_ADX_FEATURES};
use crate::cpu::detected;
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// The multiplications of P-521's field elements.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mul {
    /// The target's baseline ISA.
    Baseline,
    /// BMI2's `mulx` and ADX's `adcx` and `adox`, with the comb's selection
    /// by AVX2 (the `_adx` variants).
    #[cfg(target_arch = "x86_64")]
    Adx,
}

impl Mul {
    /// The fastest multiplications a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select(f: Features) -> Mul {
        let adx = f.contains(
            const {
                Features::all(&[
                    VG_EC_P521_PUBLIC_KEY_ADX_FEATURES,
                    VG_ECDH_P521_ADX_FEATURES,
                    VG_ECDSA_P521_SIGN_ADX_FEATURES,
                    VG_ECDSA_P521_VERIFY_ADX_FEATURES,
                ])
            },
        );
        if adx { Mul::Adx } else { Mul::Baseline }
    }

    /// The multiplications a CPU with the features `f` can run: there is
    /// only one here.
    #[cfg(not(target_arch = "x86_64"))]
    pub(crate) fn select(_: Features) -> Mul {
        Mul::Baseline
    }
}

/// The public key `Q = dG` of the key `d`, in the uncompressed form of
/// SEC 1 §2.3.3, or `None` if `d` is not in `[1, n − 1]`.
pub(crate) fn public_key(d: &[u8; 66]) -> Option<[u8; 133]> {
    let mut out = [0; 133];
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `out` is valid for reads and writes of 133 bytes, `d` for
        // reads of 66 and `scratch` for reads and writes of 8192; `out` and
        // `scratch` are distinct objects from each other and `d`, so none
        // overlaps another or the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        Mul::Baseline => unsafe { vg_ec_p521_public_key(&mut out, d, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe { vg_ec_p521_public_key_adx(&mut out, d, &mut scratch) },
    };
    zeroize(&mut scratch);
    (ok == 1).then_some(out)
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use verified_garbage_cpu::feature;

    /// The multiplications chosen with BMI2, ADX and AVX2 (and AVX, which
    /// AVX2 implies), or without one of them.
    #[test]
    fn select() {
        let cases = [
            (Features(0), Mul::Baseline),
            (Features(feature::BMI2), Mul::Baseline),
            (Features(feature::ADX), Mul::Baseline),
            (Features(feature::BMI2 | feature::ADX), Mul::Baseline),
            (
                Features(feature::AVX | feature::AVX2 | feature::BMI2),
                Mul::Baseline,
            ),
            (
                Features(feature::AVX | feature::AVX2 | feature::ADX),
                Mul::Baseline,
            ),
            (
                Features(feature::AVX | feature::AVX2 | feature::BMI2 | feature::ADX),
                Mul::Adx,
            ),
        ];
        for (f, m) in cases {
            assert_eq!(Mul::select(f), m, "{f:?}");
        }
    }
}

#[cfg(all(test, target_arch = "aarch64"))]
mod square_tests {
    use crate::arch::p521_mont::{vg_p521_mul_mod_p, vg_p521_sqr_mod_p};

    /// Differential arithmetic cases, including carries and overlapping outputs.
    #[test]
    fn square_matches_multiply() {
        let mut rng = 0x7215_84a0_e19d_a7c3u64;
        for case in 0..4096 {
            let mut a = [0u64; 9];
            for word in &mut a {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                *word = rng;
            }
            a[8] &= 511;
            match case {
                0 => a = [0; 9],
                1..=521 => {
                    a = [0; 9];
                    let bit = case - 1;
                    a[bit / 64] = 1 << (bit % 64);
                }
                522..=649 => {
                    a = [u64::MAX; 9];
                    a[8] = 511;
                    a[0] -= (case - 521) as u64;
                }
                _ => {
                    // Exclude p itself from the generated canonical inputs.
                    a[0] &= u64::MAX - 1;
                }
            }
            let mut expected = [0xa5a5_a5a5_a5a5_a5a5; 1024];
            expected[..9].copy_from_slice(&a);
            expected[9..18].copy_from_slice(&a);
            // SAFETY: all offsets and their 72-byte operands are below 3520;
            // b is canonical and the array provides the complete workspace.
            unsafe { vg_p521_mul_mod_p(&raw mut expected, 144, 0, 72) };
            for offset in [0u32, 8, 64, 72, 216, 3448] {
                let mut ws = [0xa5a5_a5a5_a5a5_a5a5; 1024];
                ws[..9].copy_from_slice(&a);
                let before = ws;
                // SAFETY: the input is canonical; input and output end at or
                // below 3520 within the full workspace. Overlap is permitted.
                unsafe { vg_p521_sqr_mod_p(&raw mut ws, offset, 0, 0) };
                let start = offset as usize / 8;
                assert_eq!(&ws[start..start + 9], &expected[18..27], "{case}/{offset}");
                assert_eq!(&ws[..start], &before[..start]);
                assert_eq!(&ws[start + 9..440], &before[start + 9..440]);
                assert_eq!(&ws[512..], &before[512..]);
            }
        }
    }
}
