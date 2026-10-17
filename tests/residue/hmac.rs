//! HMAC-SHA-256 under a secret key.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hmac::Hmac;

#[test]
fn mac() {
    super::check("hmac_sha256", || {
        let mut h = Hmac::<Sha256>::new(&super::secret()[..32]);
        h.update(b"data");
        std::hint::black_box(h.finalize());
    });
}
