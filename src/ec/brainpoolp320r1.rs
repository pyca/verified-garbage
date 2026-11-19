//! The curve brainpoolP320r1, its multiplications and public keys, which
//! ECDSA and ECDH share.

#![cfg(any(target_arch = "x86_64", target_arch = "arm", target_arch = "powerpc64"))]

use crate::align::CacheAligned;
use crate::arch::dispatch::ec_brainpoolp320r1::vg_ec_brainpoolp320r1_public_key_auto;
use crate::zeroize::zeroize;

/// The curve brainpoolP320r1 (RFC 5639 §3.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BrainpoolP320r1 {}

impl super::sealed::Sealed for BrainpoolP320r1 {
    fn public_key(dit: crate::dit::Dit<'_>, d: &[u8; 40]) -> Option<[u8; 81]> {
        public_key(dit, d)
    }
}

impl super::Curve for BrainpoolP320r1 {
    type PrivateKey = [u8; 40];
    type PublicKey = [u8; 81];
    type SharedSecret = [u8; 40];
    type Signature = [u8; 80];
}

/// The public key `Q = dG` of the key `d`, in the uncompressed form of
/// SEC 1 §2.3.3, or `None` if `d` is not in `[1, n − 1]`.
fn public_key(dit: crate::dit::Dit<'_>, d: &[u8; 40]) -> Option<[u8; 81]> {
    let mut out = [0; 81];
    let mut scratch = CacheAligned([0u64; 1024]);
    // SAFETY: `out` is valid for reads and writes of 81 bytes, `d` for reads of
    // 40 and `scratch` for reads and writes of 8192; `out` and `scratch` are
    // distinct objects from each other and `d`, so none overlaps another or the
    // call's stack frame, and, as Rust objects, none wraps around the address
    // space. The dispatcher calls only an implementation the CPU has the
    // features of.
    let ok = unsafe { vg_ec_brainpoolp320r1_public_key_auto(dit, &mut out, d, &mut scratch.0) };
    zeroize(&mut scratch.0);
    (ok == 1).then_some(out)
}
