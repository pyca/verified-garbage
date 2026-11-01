//! ML-KEM-768 (FIPS 203), the module-lattice-based key-encapsulation
//! mechanism, at security category 3.
//!
//! Key generation, encapsulation and decapsulation are the verified
//! assembly functions `vg_mlkem768_keygen`, `vg_mlkem768_encaps` and
//! `vg_mlkem768_decaps` (contracts `VG.Spec.MlKem.keyGenContract`,
//! `encapsContract` and `decapsContract`): FIPS 203's internal algorithms
//! `ML-KEM.KeyGen_internal`, `ML-KEM.Encaps_internal` and
//! `ML-KEM.Decaps_internal` (§6), which compose the verified polynomial
//! arithmetic and SHA-3. The encapsulation key check of §7.2 is
//! `vg_mlkem768_check_ek`. This module supplies their randomness and working
//! space, and destroys the intermediate values (§3.3).
//!
//! A decapsulation key is kept as the 64-byte seed `d ‖ z` it is generated
//! from (§3.3), which [`DecapsulationKey768::from_seed`] expands; the caller
//! generates the seed with an approved RBG. The expanded decapsulation key is
//! never exposed, so the decapsulation keys this module uses pass the checks
//! of §7.3 by construction. An encapsulation key from elsewhere passes the
//! check of §7.2 in [`EncapsulationKey768::from_bytes`].
//!
//! The bound on `SampleNTT`'s loop (280 iterations, as Appendix B allows) is
//! reached with probability less than 2⁻²⁶¹ for each call; key generation,
//! encapsulation and decapsulation each call it 9 times (once for each
//! entry of the matrix `Â`), so an operation reaches it with probability
//! less than 2⁻²⁵⁸, and then fails with [`Error::SampleBound`].
//!
//! On x86-64, key generation, encapsulation and decapsulation have an
//! instance for each implementation of `vg_mlkem_sample_ntt4`, which samples
//! four entries of the matrix at once, and each operation calls the best one
//! the CPU can run.
//!
//! On AArch64 with the SHA-3 extension, key generation, encapsulation and
//! decapsulation sample the matrix two entries at a time with
//! `vg_keccak_f1600_x2_sha3`, and have an instance for each single-state
//! Keccak permutation they hash with otherwise: the `_x2_sha3` instances
//! call the scalar `vg_keccak_f1600`, faster on Arm's cores, and the
//! `_x2_sha3_keccak_sha3` ones the SHA-3 extension's
//! `vg_keccak_f1600_sha3`, faster on Apple's, on which they are chosen.
//!
//! On x86-64, an [`EncapsulationKey768`] from key generation keeps the hash
//! `H(ek)` of the key (FIPS 203 §4.1), which the decapsulation key holds,
//! and encapsulation with it is `vg_mlkem768_encaps_h` (contract
//! `encapsHContract`), which takes it rather than computing it each time.
//! One from [`EncapsulationKey768::from_bytes`] does not, and encapsulation
//! with it is `vg_mlkem768_encaps`, which computes it: with AVX2, in the fourth
//! of the four Keccak states that sample the matrix three entries at a time.

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
