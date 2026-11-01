//! The implementations of AES, which everything built on it follows:
//! AES-GCM (`crate::aes_gcm`) and AES-CMAC (`crate::cmac::aes`) each choose
//! one [`Backend`], and run its key expansion directly and its counter mode
//! through their own functions for it (e.g. `vg_cmac_aes_update_aesni`
//! calls `vg_aes_ctr32_aesni`, an internal function of the verified code).
//! Those functions need the features of the counter mode they call, and may
//! need more (GCM's `vg_ghash_pclmul` needs PCLMULQDQ), so on targets with
//! more than one implementation each caller selects with
//! `Backend::select_for`, passing theirs: a CPU without them runs the scalar
//! implementation.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "aarch64")]
use crate::arch::aes::VG_AES_EXPAND_KEY_AES_FEATURES;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::VG_AES_EXPAND_KEY_AESNI_FEATURES;
use verified_garbage_cpu::Features;

/// The implementations of `vg_aes_expand_key` and `vg_aes_ctr32`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// Constant-time scalar code, for the target's baseline ISA.
    Scalar,
    /// AES-NI: the `_aesni` functions.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    AesNi,
    /// VAES: the `_vaes` functions, whose counter mode is
    /// `vg_aes_ctr32_vaes` and whose key expansion is
    /// `vg_aes_expand_key_aesni`.
    #[cfg(target_arch = "x86_64")]
    Vaes,
    /// The AES extension: the `_aes` functions.
    #[cfg(target_arch = "aarch64")]
    Aes,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run, for a
    /// caller whose own functions for AES-NI need the features `aesni`
    /// (besides those of `vg_aes_expand_key_aesni`, which this checks).
    #[cfg(target_arch = "x86")]
    pub(crate) fn select_for(f: Features, aesni: Features) -> Backend {
        if f.contains(VG_AES_EXPAND_KEY_AESNI_FEATURES) && f.contains(aesni) {
            Backend::AesNi
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run, for a
    /// caller whose own functions for VAES and for AES-NI need the features
    /// `vaes` and `aesni` (besides those of `vg_aes_expand_key_aesni`, which
    /// both run and this checks).
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select_for(f: Features, vaes: Features, aesni: Features) -> Backend {
        const OWN: Features = VG_AES_EXPAND_KEY_AESNI_FEATURES;
        if f.contains(OWN) && f.contains(vaes) {
            Backend::Vaes
        } else if f.contains(OWN) && f.contains(aesni) {
            Backend::AesNi
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run, for a
    /// caller whose own functions for the AES extension need the features
    /// `aes` (besides those of `vg_aes_expand_key_aes`, which this checks).
    #[cfg(target_arch = "aarch64")]
    pub(crate) fn select_for(f: Features, aes: Features) -> Backend {
        if f.contains(VG_AES_EXPAND_KEY_AES_FEATURES) && f.contains(aes) {
            Backend::Aes
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
    pub(crate) fn select(_: Features) -> Backend {
        Backend::Scalar
    }
}

#[cfg(test)]
mod tests {
    use super::Backend;
    use verified_garbage_cpu::Features;

    /// No features: a caller that needs none of its own.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
    const NONE: Features = Features(0);

    /// The implementation chosen for each set of features: AES-NI needs
    /// AES-NI (for the key expansion) and everything the caller's functions
    /// need (SSSE3 too, for those that run counter mode).
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn select() {
        let aes = Features(verified_garbage_cpu::feature::AES);
        let aes_ssse3 =
            Features(verified_garbage_cpu::feature::AES | verified_garbage_cpu::feature::SSSE3);
        assert_eq!(Backend::select_for(aes, aes, aes), Backend::Vaes);
        assert_eq!(Backend::select_for(aes, aes_ssse3, aes), Backend::AesNi);
        assert_eq!(
            Backend::select_for(aes_ssse3, aes_ssse3, aes_ssse3),
            Backend::Vaes
        );
        assert_eq!(
            Backend::select_for(aes, aes_ssse3, aes_ssse3),
            Backend::Scalar
        );
        for f in [Features(0), Features(verified_garbage_cpu::feature::SSSE3)] {
            assert_eq!(Backend::select_for(f, NONE, NONE), Backend::Scalar);
        }
        let all = Features(
            verified_garbage_cpu::feature::AES
                | verified_garbage_cpu::feature::PCLMULQDQ
                | verified_garbage_cpu::feature::SSSE3,
        );
        let pclmul =
            Features(verified_garbage_cpu::feature::AES | verified_garbage_cpu::feature::PCLMULQDQ);
        assert_eq!(Backend::select_for(aes_ssse3, all, pclmul), Backend::Scalar);
        assert_eq!(Backend::select_for(all, all, pclmul), Backend::Vaes);
        // VAES: everything the caller's VAES functions need (AVX2 too, for
        // counter mode); failing that, AES-NI.
        let vaes = Features(
            verified_garbage_cpu::feature::AES
                | verified_garbage_cpu::feature::AVX
                | verified_garbage_cpu::feature::AVX2
                | verified_garbage_cpu::feature::SSSE3
                | verified_garbage_cpu::feature::VAES,
        );
        assert_eq!(Backend::select_for(vaes, vaes, aes_ssse3), Backend::Vaes);
        assert_eq!(
            Backend::select_for(
                vaes,
                Features::all(&[vaes, Features(verified_garbage_cpu::feature::PCLMULQDQ)]),
                aes_ssse3
            ),
            Backend::AesNi
        );
        let no_avx2 = Features(
            verified_garbage_cpu::feature::AES
                | verified_garbage_cpu::feature::AVX
                | verified_garbage_cpu::feature::SSSE3
                | verified_garbage_cpu::feature::VAES,
        );
        assert_eq!(
            Backend::select_for(no_avx2, vaes, aes_ssse3),
            Backend::AesNi
        );
        assert_eq!(
            Backend::select_for(
                Features(
                    verified_garbage_cpu::feature::AVX
                        | verified_garbage_cpu::feature::AVX2
                        | verified_garbage_cpu::feature::VAES
                ),
                NONE,
                NONE
            ),
            Backend::Scalar
        );
    }

    /// x86 AES-NI needs AES, while each caller adds its own requirements.
    #[cfg(target_arch = "x86")]
    #[test]
    fn select() {
        let aes = Features(verified_garbage_cpu::feature::AES);
        assert_eq!(Backend::select_for(aes, NONE), Backend::AesNi);
        assert_eq!(
            Backend::select_for(aes, Features(verified_garbage_cpu::feature::AES)),
            Backend::AesNi
        );
        for f in [Features(0), Features(verified_garbage_cpu::feature::SSSE3)] {
            assert_eq!(Backend::select_for(f, NONE), Backend::Scalar);
        }
        assert_eq!(
            Backend::select_for(aes, Features(verified_garbage_cpu::feature::SSSE3)),
            Backend::Scalar
        );
        assert_eq!(
            Backend::select_for(aes, Features(verified_garbage_cpu::feature::PCLMULQDQ)),
            Backend::Scalar
        );
        let all = Features(
            verified_garbage_cpu::feature::AES
                | verified_garbage_cpu::feature::PCLMULQDQ
                | verified_garbage_cpu::feature::SSSE3,
        );
        assert_eq!(
            Backend::select_for(
                all,
                Features(
                    verified_garbage_cpu::feature::PCLMULQDQ | verified_garbage_cpu::feature::SSSE3
                )
            ),
            Backend::AesNi
        );
    }

    /// The implementation chosen for each set of features.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn select() {
        let aes = Features(verified_garbage_cpu::feature::AES);
        assert_eq!(Backend::select_for(aes, NONE), Backend::Aes);
        assert_eq!(
            Backend::select_for(aes, Features(verified_garbage_cpu::feature::AES)),
            Backend::Aes
        );
        assert_eq!(Backend::select_for(Features(0), NONE), Backend::Scalar);
        assert_eq!(
            Backend::select_for(aes, Features(verified_garbage_cpu::feature::SHA2)),
            Backend::Scalar
        );
    }

    /// The scalar implementation is the only one.
    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
    #[test]
    fn select() {
        assert_eq!(Backend::select(Features(0)), Backend::Scalar);
    }
}
