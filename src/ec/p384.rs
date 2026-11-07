//! P-384's multiplications and public keys, which ECDSA and ECDH share.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::ec_p384::vg_ec_p384_public_key_auto;
use crate::zeroize::zeroize;

/// The public key `Q = dG` of the key `d`, in the uncompressed form of
/// SEC 1 §2.3.3, or `None` if `d` is not in `[1, n − 1]`.
pub(crate) fn public_key(d: &[u8; 48]) -> Option<[u8; 97]> {
    let mut out = [0; 97];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` is valid for reads and writes of 97 bytes, `d` for reads of
    // 48 and `scratch` for reads and writes of 8192; `out` and `scratch` are
    // distinct objects from each other and `d`, so none overlaps another or the
    // call's stack frame, and, as Rust objects, none wraps around the address
    // space. The dispatcher calls only an implementation the CPU has the
    // features of.
    let ok = unsafe { vg_ec_p384_public_key_auto(&mut out, d, &mut scratch) };
    zeroize(&mut scratch);
    (ok == 1).then_some(out)
}
