//! Differential checks of both key sizes, empty inputs, tails and batch boundaries.
#![cfg(feature = "openssl-gcm-siv")]
#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[path = "../support/openssl_gcm_siv.rs"]
mod oracle;

use openssl::cipher::Cipher;
use verified_garbage::aead::aes_gcm_siv::AesGcmSiv;

#[test]
fn matches_openssl() {
    let mut sizes: Vec<usize> = (0..=257).collect();
    for center in [512, 1024, 2048, 4096, 16384] {
        sizes.extend(center - 17..=center + 17);
    }
    sizes.push(1048576);
    for key_len in [16, 32] {
        let key = vec![0x42; key_len];
        let cipher = Cipher::fetch(None, &format!("AES-{}-GCM-SIV", key_len * 8), None).unwrap();
        let k = AesGcmSiv::new(&key).unwrap();
        for &n in &sizes {
            let nonce = [0x24; 12];
            let aad_len = [n % 65, 127, 128, 129][n % 4];
            let aad: Vec<u8> = (0..aad_len).map(|i| (i * 31) as u8).collect();
            let plain: Vec<u8> = (0..n).map(|i| (i * 73 + n) as u8).collect();
            let mut expected = plain.clone();
            let tag = oracle::seal(&cipher, &key, &nonce, &aad, &mut expected);
            let mut guarded = vec![0xa5; n + 2];
            guarded[1..n + 1].copy_from_slice(&plain);
            assert_eq!(
                k.encrypt_in_place(&nonce, &aad, &mut guarded[1..n + 1])
                    .unwrap(),
                tag
            );
            assert_eq!(&guarded[1..n + 1], expected, "n={n}, key={key_len}");
            let ciphertext = expected.clone();
            oracle::open(&cipher, &key, &nonce, &aad, &mut expected, &tag).unwrap();
            assert_eq!(expected, plain);
            k.decrypt_in_place(&nonce, &aad, &mut guarded[1..n + 1], &tag)
                .unwrap();
            assert_eq!(&guarded[1..n + 1], plain);
            guarded[1..n + 1].copy_from_slice(&ciphertext);
            let mut bad = tag;
            bad[15] ^= 1;
            assert!(
                k.decrypt_in_place(&nonce, &aad, &mut guarded[1..n + 1], &bad)
                    .is_err()
            );
            assert!(guarded[1..n + 1].iter().all(|&b| b == 0));
            assert_eq!((guarded[0], guarded[n + 1]), (0xa5, 0xa5));
        }
    }
}
