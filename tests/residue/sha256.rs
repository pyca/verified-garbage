//! SHA-256 of a secret message.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha256::Sha256;

#[test]
fn digest() {
    super::check("sha256", || {
        let mut h = Sha256::new();
        h.update(super::secret());
        std::hint::black_box(h.finalize());
    });
}
