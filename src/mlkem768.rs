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
    check_ek: crate::arch::dispatch::mlkem768::vg_mlkem768_check_ek_auto,
    keygen: crate::arch::dispatch::mlkem768::vg_mlkem768_keygen_auto,
    encaps: crate::arch::dispatch::mlkem768::vg_mlkem768_encaps_auto,
    decaps: crate::arch::dispatch::mlkem768::vg_mlkem768_decaps_auto,
    encaps_h: crate::arch::dispatch::mlkem768::vg_mlkem768_encaps_h_auto,
    ek: 1184,
    dk: 2400,
    ct: 1088,
    scratch: 4096,
}
