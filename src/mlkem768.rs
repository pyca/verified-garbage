//! ML-KEM-768 (FIPS 203), the module-lattice-based key-encapsulation mechanism,
//! at security category 3.
//!
//! A decapsulation key is the 64-byte seed `d ‖ z` it is generated from
//! ([`DecapsulationKey768::from_seed`]), which the caller generates with an
//! approved RBG; the expanded key is never exposed, so it passes the checks of
//! §7.3 by construction. An encapsulation key from elsewhere passes the check
//! of §7.2 in [`EncapsulationKey768::from_bytes`]. An operation fails with
//! [`MlKemError::SampleBound`] if it reaches the bound on `SampleNTT`'s loop
//! that Appendix B allows, with probability less than 2⁻²⁵⁸.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

crate::mlkem_common::ml_kem! {
    name: "ML-KEM-768",
    encapsulation_key: EncapsulationKey768,
    decapsulation_key: DecapsulationKey768,
    check_ek: crate::arch::mlkem768::vg_mlkem768_check_ek,
    keygen: crate::arch::mlkem768::vg_mlkem768_keygen,
    encaps: crate::arch::mlkem768::vg_mlkem768_encaps,
    decaps: crate::arch::mlkem768::vg_mlkem768_decaps,
    encaps_h: crate::arch::mlkem768::vg_mlkem768_encaps_h,
    keygen_x2_sha3: (crate::arch::mlkem768::vg_mlkem768_keygen_x2_sha3, crate::arch::mlkem768::VG_MLKEM768_KEYGEN_X2_SHA3_FEATURES),
    encaps_x2_sha3: (crate::arch::mlkem768::vg_mlkem768_encaps_x2_sha3, crate::arch::mlkem768::VG_MLKEM768_ENCAPS_X2_SHA3_FEATURES),
    decaps_x2_sha3: (crate::arch::mlkem768::vg_mlkem768_decaps_x2_sha3, crate::arch::mlkem768::VG_MLKEM768_DECAPS_X2_SHA3_FEATURES),
    encaps_h_x2_sha3: (crate::arch::mlkem768::vg_mlkem768_encaps_h_x2_sha3, crate::arch::mlkem768::VG_MLKEM768_ENCAPS_H_X2_SHA3_FEATURES),
    keygen_x2_sha3_keccak_sha3: (
        crate::arch::mlkem768::vg_mlkem768_keygen_x2_sha3_keccak_sha3,
        crate::arch::mlkem768::VG_MLKEM768_KEYGEN_X2_SHA3_KECCAK_SHA3_FEATURES,
    ),
    encaps_x2_sha3_keccak_sha3: (
        crate::arch::mlkem768::vg_mlkem768_encaps_x2_sha3_keccak_sha3,
        crate::arch::mlkem768::VG_MLKEM768_ENCAPS_X2_SHA3_KECCAK_SHA3_FEATURES,
    ),
    decaps_x2_sha3_keccak_sha3: (
        crate::arch::mlkem768::vg_mlkem768_decaps_x2_sha3_keccak_sha3,
        crate::arch::mlkem768::VG_MLKEM768_DECAPS_X2_SHA3_KECCAK_SHA3_FEATURES,
    ),
    encaps_h_x2_sha3_keccak_sha3: (
        crate::arch::mlkem768::vg_mlkem768_encaps_h_x2_sha3_keccak_sha3,
        crate::arch::mlkem768::VG_MLKEM768_ENCAPS_H_X2_SHA3_KECCAK_SHA3_FEATURES,
    ),
    keygen_avx: (crate::arch::mlkem768::vg_mlkem768_keygen_avx, crate::arch::mlkem768::VG_MLKEM768_KEYGEN_AVX_FEATURES),
    encaps_h_avx: (crate::arch::mlkem768::vg_mlkem768_encaps_h_avx, crate::arch::mlkem768::VG_MLKEM768_ENCAPS_H_AVX_FEATURES),
    encaps_avx: (crate::arch::mlkem768::vg_mlkem768_encaps_avx, crate::arch::mlkem768::VG_MLKEM768_ENCAPS_AVX_FEATURES),
    decaps_avx: (crate::arch::mlkem768::vg_mlkem768_decaps_avx, crate::arch::mlkem768::VG_MLKEM768_DECAPS_AVX_FEATURES),
    keygen_avx2: (crate::arch::mlkem768::vg_mlkem768_keygen_avx2, crate::arch::mlkem768::VG_MLKEM768_KEYGEN_AVX2_FEATURES),
    keygen_avx512: (crate::arch::mlkem768::vg_mlkem768_keygen_avx512, crate::arch::mlkem768::VG_MLKEM768_KEYGEN_AVX512_FEATURES),
    encaps_h_avx2: (crate::arch::mlkem768::vg_mlkem768_encaps_h_avx2, crate::arch::mlkem768::VG_MLKEM768_ENCAPS_H_AVX2_FEATURES),
    encaps_h_avx512: (crate::arch::mlkem768::vg_mlkem768_encaps_h_avx512, crate::arch::mlkem768::VG_MLKEM768_ENCAPS_H_AVX512_FEATURES),
    encaps_avx2: (crate::arch::mlkem768::vg_mlkem768_encaps_avx2, crate::arch::mlkem768::VG_MLKEM768_ENCAPS_AVX2_FEATURES),
    encaps_avx512: (crate::arch::mlkem768::vg_mlkem768_encaps_avx512, crate::arch::mlkem768::VG_MLKEM768_ENCAPS_AVX512_FEATURES),
    decaps_avx2: (crate::arch::mlkem768::vg_mlkem768_decaps_avx2, crate::arch::mlkem768::VG_MLKEM768_DECAPS_AVX2_FEATURES),
    decaps_avx512: (crate::arch::mlkem768::vg_mlkem768_decaps_avx512, crate::arch::mlkem768::VG_MLKEM768_DECAPS_AVX512_FEATURES),
    check_ek_avx2: (crate::arch::mlkem768::vg_mlkem768_check_ek_avx2, crate::arch::mlkem768::VG_MLKEM768_CHECK_EK_AVX2_FEATURES),
    ek: 1184,
    dk: 2400,
    ct: 1088,
    scratch: 4096,
}
