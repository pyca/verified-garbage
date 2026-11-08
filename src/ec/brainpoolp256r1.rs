//! brainpoolP256r1's multiplications and public keys, which ECDSA and ECDH
//! share.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::ec_brainpoolp256r1::vg_ec_brainpoolp256r1_public_key_auto;
use crate::zeroize::zeroize;

/// The public key `Q = dG` of the key `d`, in the uncompressed form of
/// SEC 1 §2.3.3, or `None` if `d` is not in `[1, n − 1]`.
pub(crate) fn public_key(d: &[u8; 32]) -> Option<[u8; 65]> {
    let mut out = [0; 65];
    let mut scratch = CacheAligned([0u64; 1024]);
    // SAFETY: `out` is valid for reads and writes of 65 bytes, `d` for reads of
    // 32 and `scratch` for reads and writes of 8192; `out` and `scratch` are
    // distinct objects from each other and `d`, so none overlaps another or the
    // call's stack frame, and, as Rust objects, none wraps around the address
    // space. The dispatcher calls only an implementation the CPU has the
    // features of.
    let ok = unsafe { vg_ec_brainpoolp256r1_public_key_auto(&mut out, d, &mut scratch.0) };
    zeroize(&mut scratch.0);
    (ok == 1).then_some(out)
}
