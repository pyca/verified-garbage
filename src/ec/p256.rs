//! P-256's multiplications, which [`ecdsa`](crate::ecdsa) and
//! [`ecdh`](crate::ecdh) choose between, and its public keys, which both
//! compute. On x86-64 CPUs with BMI2, ADX and AVX2, the `_adx` variants
//! multiply field elements and scalars with `mulx`, `adcx` and `adox`, and
//! the signatures' and public keys' comb selects its entries with AVX2.

use crate::arch::ec_p256::vg_ec_p256_public_key;
#[cfg(target_arch = "x86_64")]
use crate::arch::ec_p256::{VG_EC_P256_PUBLIC_KEY_ADX_FEATURES, vg_ec_p256_public_key_adx};
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdh_p256::VG_ECDH_P256_ADX_FEATURES;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p256::{VG_ECDSA_P256_SIGN_ADX_FEATURES, VG_ECDSA_P256_VERIFY_ADX_FEATURES};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// The multiplications of P-256's field elements and scalars.
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
                    VG_EC_P256_PUBLIC_KEY_ADX_FEATURES,
                    VG_ECDH_P256_ADX_FEATURES,
                    VG_ECDSA_P256_SIGN_ADX_FEATURES,
                    VG_ECDSA_P256_VERIFY_ADX_FEATURES,
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
pub(crate) fn public_key(d: &[u8; 32]) -> Option<[u8; 65]> {
    let mut out = [0; 65];
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `out` is valid for reads and writes of 65 bytes, `d` for
        // reads of 32 and `scratch` for reads and writes of 8192; `out` and
        // `scratch` are distinct objects from each other and `d`, so none
        // overlaps another or the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        Mul::Baseline => unsafe { vg_ec_p256_public_key(&mut out, d, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe { vg_ec_p256_public_key_adx(&mut out, d, &mut scratch) },
    };
    zeroize(&mut scratch);
    (ok == 1).then_some(out)
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;

    /// The multiplications chosen with BMI2, ADX and AVX2 (and AVX, which
    /// AVX2 implies), or without one of them.
    #[test]
    fn select() {
        let cases = [
            (Features::of(&[]), Mul::Baseline),
            (Features::of(&["bmi2"]), Mul::Baseline),
            (Features::of(&["adx"]), Mul::Baseline),
            (Features::of(&["bmi2", "adx"]), Mul::Baseline),
            (Features::of(&["avx", "avx2", "bmi2"]), Mul::Baseline),
            (Features::of(&["avx", "avx2", "adx"]), Mul::Baseline),
            (Features::of(&["avx", "avx2", "bmi2", "adx"]), Mul::Adx),
        ];
        for (f, m) in cases {
            assert_eq!(Mul::select(f), m, "{f:?}");
        }
    }
}
