//! secp256k1's multiplications, which [`ecdsa`](crate::ecdsa) and
//! [`ecdh`](crate::ecdh) choose between, and its public keys, which both
//! compute. `Mul::select` chooses the `_umaal` variants on ARMv7 CPUs with
//! the features their `_FEATURES` constants name.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use crate::arch::ec_secp256k1::vg_ec_secp256k1_public_key;
#[cfg(target_arch = "arm")]
use crate::arch::ec_secp256k1::{
    VG_EC_SECP256K1_PUBLIC_KEY_UMAAL_FEATURES, vg_ec_secp256k1_public_key_umaal,
};
#[cfg(target_arch = "arm")]
use crate::arch::ecdh_secp256k1::VG_ECDH_SECP256K1_UMAAL_FEATURES;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_secp256k1::VG_ECDSA_SECP256K1_VERIFY_UMAAL_FEATURES;
#[cfg(target_arch = "arm")]
use crate::arch::ecdsa_secp256k1_sha256::VG_ECDSA_SECP256K1_SHA256_SIGN_UMAAL_FEATURES;
use crate::cpu::detected;
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// The multiplications of secp256k1's field elements.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mul {
    /// The baseline implementation.
    Baseline,
    /// `_umaal`.
    #[cfg(target_arch = "arm")]
    Umaal,
}

impl Mul {
    /// The fastest multiplications a CPU with the features `f` can run.
    #[cfg(target_arch = "arm")]
    pub(crate) fn select(f: Features) -> Mul {
        let umaal = f.contains(
            const {
                Features::all(&[
                    VG_EC_SECP256K1_PUBLIC_KEY_UMAAL_FEATURES,
                    VG_ECDH_SECP256K1_UMAAL_FEATURES,
                    VG_ECDSA_SECP256K1_SHA256_SIGN_UMAAL_FEATURES,
                    VG_ECDSA_SECP256K1_VERIFY_UMAAL_FEATURES,
                ])
            },
        );
        if umaal { Mul::Umaal } else { Mul::Baseline }
    }

    /// The multiplications a CPU with the features `f` can run: there is
    /// only one here.
    #[cfg(not(target_arch = "arm"))]
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
        Mul::Baseline => unsafe { vg_ec_secp256k1_public_key(&mut out, d, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
        // (`Mul::select`).
        #[cfg(target_arch = "arm")]
        Mul::Umaal => unsafe { vg_ec_secp256k1_public_key_umaal(&mut out, d, &mut scratch) },
    };
    zeroize(&mut scratch);
    (ok == 1).then_some(out)
}

#[cfg(all(test, target_arch = "arm"))]
mod tests {
    use super::*;
    use verified_garbage_cpu::feature;

    /// The multiplications chosen with `umaal`, or without it.
    #[test]
    fn select() {
        assert_eq!(Mul::select(Features(0)), Mul::Baseline);
        assert_eq!(Mul::select(Features(feature::UMAAL)), Mul::Umaal);
    }
}
