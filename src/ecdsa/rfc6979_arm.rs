//! The verified `vg_ecdsa_<curve>_rfc6979_sign` of 32-bit ARM: one
//! implementation of each, for every CPU (ARM has one implementation of
//! each hash function, so one tier).

#![cfg(target_arch = "arm")]

use super::rfc6979::SignFn;
use crate::arch::ecdsa_brainpoolp256r1_rfc6979::vg_ecdsa_brainpoolp256r1_rfc6979_sign;
use crate::arch::ecdsa_brainpoolp384r1_rfc6979::vg_ecdsa_brainpoolp384r1_rfc6979_sign;
use crate::arch::ecdsa_brainpoolp512r1_rfc6979::vg_ecdsa_brainpoolp512r1_rfc6979_sign;
use crate::arch::ecdsa_p192_rfc6979::vg_ecdsa_p192_rfc6979_sign;
use crate::arch::ecdsa_p224_rfc6979::vg_ecdsa_p224_rfc6979_sign;
use crate::arch::ecdsa_p256_rfc6979::vg_ecdsa_p256_rfc6979_sign;
use crate::arch::ecdsa_p384_rfc6979::vg_ecdsa_p384_rfc6979_sign;
use crate::arch::ecdsa_p521_rfc6979::vg_ecdsa_p521_rfc6979_sign;
use crate::arch::ecdsa_secp256k1_rfc6979::vg_ecdsa_secp256k1_rfc6979_sign;
use crate::cpu::Features;

/// `vg_ecdsa_p192_rfc6979_sign`, which every CPU runs.
pub(super) fn p192(_f: Features) -> SignFn<24, 48> {
    vg_ecdsa_p192_rfc6979_sign
}

/// `vg_ecdsa_p224_rfc6979_sign`, which every CPU runs.
pub(super) fn p224(_f: Features) -> SignFn<28, 56> {
    vg_ecdsa_p224_rfc6979_sign
}

/// `vg_ecdsa_p256_rfc6979_sign`, which every CPU runs.
pub(super) fn p256(_f: Features) -> SignFn<32, 64> {
    vg_ecdsa_p256_rfc6979_sign
}

/// `vg_ecdsa_p384_rfc6979_sign`, which every CPU runs.
pub(super) fn p384(_f: Features) -> SignFn<48, 96> {
    vg_ecdsa_p384_rfc6979_sign
}

/// `vg_ecdsa_p521_rfc6979_sign`, which every CPU runs.
pub(super) fn p521(_f: Features) -> SignFn<66, 132> {
    vg_ecdsa_p521_rfc6979_sign
}

/// `vg_ecdsa_brainpoolp256r1_rfc6979_sign`, which every CPU runs.
pub(super) fn brainpoolp256r1(_f: Features) -> SignFn<32, 64> {
    vg_ecdsa_brainpoolp256r1_rfc6979_sign
}

/// `vg_ecdsa_brainpoolp384r1_rfc6979_sign`, which every CPU runs.
pub(super) fn brainpoolp384r1(_f: Features) -> SignFn<48, 96> {
    vg_ecdsa_brainpoolp384r1_rfc6979_sign
}

/// `vg_ecdsa_brainpoolp512r1_rfc6979_sign`, which every CPU runs.
pub(super) fn brainpoolp512r1(_f: Features) -> SignFn<64, 128> {
    vg_ecdsa_brainpoolp512r1_rfc6979_sign
}

/// `vg_ecdsa_secp256k1_rfc6979_sign`, which every CPU runs.
pub(super) fn secp256k1(_f: Features) -> SignFn<32, 64> {
    vg_ecdsa_secp256k1_rfc6979_sign
}
