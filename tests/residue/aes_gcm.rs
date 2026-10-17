//! AES-128-GCM under a secret key.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use verified_garbage::aes_gcm::AesGcm;

#[test]
fn seal() {
    super::check("aes_gcm", || {
        let k = AesGcm::new(&super::secret()[..16]).unwrap();
        let mut data = [0u8; 40];
        std::hint::black_box(k.encrypt_in_place(&[0; 12], &[], &mut data).unwrap());
    });
}
