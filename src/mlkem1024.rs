//! ML-KEM-1024 (FIPS 203), the module-lattice-based key-encapsulation
//! mechanism, at security category 5.
//!
//! A decapsulation key is the 64-byte seed `d ‖ z` it is generated from
//! ([`DecapsulationKey1024::from_seed`]), which the caller generates with an
//! approved RBG; the expanded key is never exposed, so it passes the checks of
//! §7.3 by construction. An encapsulation key from elsewhere passes the check
//! of §7.2 in [`EncapsulationKey1024::from_bytes`]. An operation fails with
//! [`MlKemError::SampleBound`] if it reaches the bound on `SampleNTT`'s loop
//! that Appendix B allows, with probability less than 2⁻²⁵⁷.

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
    check_ek: crate::arch::dispatch::mlkem1024::vg_mlkem1024_check_ek_auto,
    keygen: crate::arch::dispatch::mlkem1024::vg_mlkem1024_keygen_auto,
    encaps: crate::arch::dispatch::mlkem1024::vg_mlkem1024_encaps_auto,
    decaps: crate::arch::dispatch::mlkem1024::vg_mlkem1024_decaps_auto,
    encaps_h: crate::arch::dispatch::mlkem1024::vg_mlkem1024_encaps_h_auto,
    ek: 1568,
    dk: 3168,
    ct: 1568,
    scratch: 6144,
}
