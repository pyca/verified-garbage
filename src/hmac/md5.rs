//! HMAC-MD5: `vg_hmac_md5_init`, `vg_md5_update` and `vg_hmac_md5_finalize`
//! (contracts `VG.Spec.Hmac.Instance.initAnyKeyContract` of
//! `VG.Spec.Hmac.md5I`, `VG.Spec.Md5.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute HMAC with a key of any
//! length, `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))` (`VG.Spec.Hmac.hmac`),
//! keeping the two MD5 streaming states.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::hmac_md5::{vg_hmac_md5_finalize, vg_hmac_md5_init};
use crate::hashes::md5::{Md5, Md5Backend};

super::streaming_hmac!(
    Md5 (Md5Backend) {
        Scalar => (vg_hmac_md5_init, vg_hmac_md5_finalize),
    },
    state: 80,
    output: 16,
);
