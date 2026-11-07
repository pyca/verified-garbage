//! P-521's multiplications and public keys, which ECDSA and ECDH share.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::ec_p521::vg_ec_p521_public_key_auto;
#[cfg(target_arch = "x86_64")]
use crate::arch::ec_p521::VG_EC_P521_PUBLIC_KEY_ADX_FEATURES;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdh_p521::VG_ECDH_P521_ADX_FEATURES;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p521::{VG_ECDSA_P521_SIGN_ADX_FEATURES, VG_ECDSA_P521_VERIFY_ADX_FEATURES};
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// The multiplications of P-521's field elements.
///
/// Only ECDSA signing still chooses by it: it passes its function, with the
/// HMAC table, to `ecdsa::table::sign_with`. The other operations call their
/// generated dispatchers (`crate::arch::dispatch`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mul {
    /// The baseline implementation.
    Baseline,
    /// `_adx`.
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
pub(crate) fn public_key(dit: crate::dit::Dit<'_>, d: &[u8; 66]) -> Option<[u8; 133]> {
    let mut out = [0; 133];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` is valid for reads and writes of 133 bytes, `d` for reads
    // of 66 and `scratch` for reads and writes of 8192; `out` and `scratch` are
    // distinct objects from each other and `d`, so none overlaps another or the
    // call's stack frame, and, as Rust objects, none wraps around the address
    // space. The dispatcher calls only an implementation the CPU has the
    // features of.
    let ok = unsafe { vg_ec_p521_public_key_auto(dit, &mut out, d, &mut scratch) };
    zeroize(&mut scratch);
    (ok == 1).then_some(out)
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::{Features, Mul};
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
