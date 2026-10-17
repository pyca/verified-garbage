//! ChaCha20-Poly1305 under a secret key.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::chacha20poly1305::ChaCha20Poly1305;

#[test]
fn seal() {
    super::check("chacha20poly1305", || {
        let k = ChaCha20Poly1305::new(super::secret()[..32].try_into().unwrap());
        let mut data = [0u8; 40];
        std::hint::black_box(k.encrypt_in_place(&[0; 12], &[], &mut data).unwrap());
    });
}
