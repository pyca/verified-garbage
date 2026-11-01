//! ML-KEM-1024 (FIPS 203), the module-lattice-based key-encapsulation
//! mechanism, at security category 5.
//!
//! Key generation, encapsulation and decapsulation are the verified
//! assembly functions `vg_mlkem1024_keygen`, `vg_mlkem1024_encaps` and
//! `vg_mlkem1024_decaps` (contracts `VG.Spec.MlKem1024.keyGenContract`,
//! `encapsContract` and `decapsContract`): FIPS 203's internal algorithms
//! `ML-KEM.KeyGen_internal`, `ML-KEM.Encaps_internal` and
//! `ML-KEM.Decaps_internal` (§6). The encapsulation key check of §7.2 is
//! `vg_mlkem1024_check_ek`. This module supplies their randomness and
//! working space, and destroys the intermediate values (§3.3).
//!
//! A decapsulation key is kept as the 64-byte seed `d ‖ z` it is generated
//! from (§3.3), which [`DecapsulationKey1024::from_seed`] expands; the caller
//! generates the seed with an approved RBG. The expanded decapsulation key is
//! never exposed, so the decapsulation keys this module uses pass the checks
//! of §7.3 by construction. An encapsulation key from elsewhere passes the
//! check of §7.2 in [`EncapsulationKey1024::from_bytes`].
//!
//! The bound on `SampleNTT`'s loop (280 iterations, as Appendix B allows) is
//! reached with probability less than 2⁻²⁶¹ for each call; key generation,
//! encapsulation and decapsulation each call it 16 times (once for each
//! entry of the matrix `Â`), so an operation reaches it with probability
//! less than 2⁻²⁵⁷, and then fails with [`Error::SampleBound`].
//!
//! Their instances, with the same contracts, are chosen by
//! `crate::mlkem_common::Backend::select`, on CPUs with the features their
//! `_FEATURES` constants name: on x86-64, the `_avx512` ones, then the
//! `_avx2` ones; on AArch64, the `_x2_sha3_keccak_sha3` ones on Apple's
//! cores and the `_x2_sha3` ones on others.
//!
//! On x86-64, an [`EncapsulationKey1024`] from key generation keeps the hash
//! `H(ek)` of the key (FIPS 203 §4.1), which the decapsulation key holds,
//! and encapsulation with it is `vg_mlkem1024_encaps_h` (contract
//! `encapsHContract`), which takes it rather than computing it each time.
//! One from [`EncapsulationKey1024::from_bytes`] does not, and encapsulation
//! with it is `vg_mlkem1024_encaps`, which computes it.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

crate::mlkem_common::ml_kem! {
    name: "ML-KEM-1024",
    encapsulation_key: EncapsulationKey1024,
    decapsulation_key: DecapsulationKey1024,
    check_ek: crate::arch::mlkem1024::vg_mlkem1024_check_ek,
    keygen: crate::arch::mlkem1024::vg_mlkem1024_keygen,
    encaps: crate::arch::mlkem1024::vg_mlkem1024_encaps,
    decaps: crate::arch::mlkem1024::vg_mlkem1024_decaps,
    encaps_h: crate::arch::mlkem1024::vg_mlkem1024_encaps_h,
    keygen_x2_sha3: (crate::arch::mlkem1024::vg_mlkem1024_keygen_x2_sha3, crate::arch::mlkem1024::VG_MLKEM1024_KEYGEN_X2_SHA3_FEATURES),
    encaps_x2_sha3: (crate::arch::mlkem1024::vg_mlkem1024_encaps_x2_sha3, crate::arch::mlkem1024::VG_MLKEM1024_ENCAPS_X2_SHA3_FEATURES),
    decaps_x2_sha3: (crate::arch::mlkem1024::vg_mlkem1024_decaps_x2_sha3, crate::arch::mlkem1024::VG_MLKEM1024_DECAPS_X2_SHA3_FEATURES),
    keygen_x2_sha3_keccak_sha3: (
        crate::arch::mlkem1024::vg_mlkem1024_keygen_x2_sha3_keccak_sha3,
        crate::arch::mlkem1024::VG_MLKEM1024_KEYGEN_X2_SHA3_KECCAK_SHA3_FEATURES,
    ),
    encaps_x2_sha3_keccak_sha3: (
        crate::arch::mlkem1024::vg_mlkem1024_encaps_x2_sha3_keccak_sha3,
        crate::arch::mlkem1024::VG_MLKEM1024_ENCAPS_X2_SHA3_KECCAK_SHA3_FEATURES,
    ),
    decaps_x2_sha3_keccak_sha3: (
        crate::arch::mlkem1024::vg_mlkem1024_decaps_x2_sha3_keccak_sha3,
        crate::arch::mlkem1024::VG_MLKEM1024_DECAPS_X2_SHA3_KECCAK_SHA3_FEATURES,
    ),
    keygen_avx2: (crate::arch::mlkem1024::vg_mlkem1024_keygen_avx2, crate::arch::mlkem1024::VG_MLKEM1024_KEYGEN_AVX2_FEATURES),
    keygen_avx512: (crate::arch::mlkem1024::vg_mlkem1024_keygen_avx512, crate::arch::mlkem1024::VG_MLKEM1024_KEYGEN_AVX512_FEATURES),
    encaps_h_avx2: (crate::arch::mlkem1024::vg_mlkem1024_encaps_h_avx2, crate::arch::mlkem1024::VG_MLKEM1024_ENCAPS_H_AVX2_FEATURES),
    encaps_h_avx512: (crate::arch::mlkem1024::vg_mlkem1024_encaps_h_avx512, crate::arch::mlkem1024::VG_MLKEM1024_ENCAPS_H_AVX512_FEATURES),
    encaps_avx2: (crate::arch::mlkem1024::vg_mlkem1024_encaps_avx2, crate::arch::mlkem1024::VG_MLKEM1024_ENCAPS_AVX2_FEATURES),
    encaps_avx512: (crate::arch::mlkem1024::vg_mlkem1024_encaps_avx512, crate::arch::mlkem1024::VG_MLKEM1024_ENCAPS_AVX512_FEATURES),
    decaps_avx2: (crate::arch::mlkem1024::vg_mlkem1024_decaps_avx2, crate::arch::mlkem1024::VG_MLKEM1024_DECAPS_AVX2_FEATURES),
    decaps_avx512: (crate::arch::mlkem1024::vg_mlkem1024_decaps_avx512, crate::arch::mlkem1024::VG_MLKEM1024_DECAPS_AVX512_FEATURES),
    check_ek_avx2: (crate::arch::mlkem1024::vg_mlkem1024_check_ek_avx2, crate::arch::mlkem1024::VG_MLKEM1024_CHECK_EK_AVX2_FEATURES),
    ek: 1568,
    dk: 3168,
    ct: 1568,
    scratch: 6144,
    scratch_written: {
        keygen: (
            crate::arch::mlkem1024::VG_MLKEM1024_KEYGEN_AVX2_SCRATCH_WRITTEN,
            crate::arch::mlkem1024::VG_MLKEM1024_KEYGEN_AVX512_SCRATCH_WRITTEN,
        ),
        encaps_h: (
            crate::arch::mlkem1024::VG_MLKEM1024_ENCAPS_H_AVX2_SCRATCH_WRITTEN,
            crate::arch::mlkem1024::VG_MLKEM1024_ENCAPS_H_AVX512_SCRATCH_WRITTEN,
        ),
        encaps: (
            crate::arch::mlkem1024::VG_MLKEM1024_ENCAPS_AVX2_SCRATCH_WRITTEN,
            crate::arch::mlkem1024::VG_MLKEM1024_ENCAPS_AVX512_SCRATCH_WRITTEN,
        ),
        decaps: (
            crate::arch::mlkem1024::VG_MLKEM1024_DECAPS_AVX2_SCRATCH_WRITTEN,
            crate::arch::mlkem1024::VG_MLKEM1024_DECAPS_AVX512_SCRATCH_WRITTEN,
        ),
    },
}
