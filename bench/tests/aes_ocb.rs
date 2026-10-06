//! Differential checks against OpenSSL around OCB batch and tail boundaries.
#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use openssl::{cipher::Cipher, cipher_ctx::CipherCtx};
use verified_garbage::aes_ocb::AesOcb;

fn compare<const T: usize>(key: &[u8], cipher: &openssl::cipher::CipherRef, n: usize) {
    let nonce = vec![0x24; 1 + n % 15];
    let aad: Vec<u8> = (0..n % 65).map(|i| (i * 31) as u8).collect();
    let plain: Vec<u8> = (0..n).map(|i| (i * 73 + n) as u8).collect();
    let mut ctx = CipherCtx::new().unwrap();
    ctx.encrypt_init(Some(cipher), None, None).unwrap();
    ctx.set_iv_length(nonce.len()).unwrap();
    ctx.set_tag_length(T).unwrap();
    ctx.encrypt_init(None, Some(key), Some(&nonce)).unwrap();
    ctx.cipher_update(&aad, None).unwrap();
    let mut ciphertext = vec![0; n + 16];
    let count = ctx.cipher_update(&plain, Some(&mut ciphertext)).unwrap();
    let count = count + ctx.cipher_final(&mut ciphertext[count..]).unwrap();
    ciphertext.truncate(count);
    let mut expected_tag = [0; T];
    ctx.tag(&mut expected_tag).unwrap();

    let k = AesOcb::new(key).unwrap();
    let mut guarded = vec![0xa5; n + 2];
    guarded[1..n + 1].copy_from_slice(&plain);
    let tag = k
        .encrypt_in_place::<T>(&nonce, &aad, &mut guarded[1..n + 1])
        .unwrap();
    assert_eq!(
        &guarded[1..n + 1],
        ciphertext,
        "ciphertext: n={n}, key={}, tag={T}",
        key.len()
    );
    assert_eq!(tag, expected_tag, "tag: n={n}, key={}, tag={T}", key.len());
    assert_eq!((guarded[0], guarded[n + 1]), (0xa5, 0xa5));
    k.decrypt_in_place(&nonce, &aad, &mut guarded[1..n + 1], &expected_tag)
        .unwrap();
    assert_eq!(&guarded[1..n + 1], plain);
    assert_eq!((guarded[0], guarded[n + 1]), (0xa5, 0xa5));
    guarded[1..n + 1].copy_from_slice(&ciphertext);
    expected_tag[T - 1] ^= 1;
    assert!(
        k.decrypt_in_place(&nonce, &aad, &mut guarded[1..n + 1], &expected_tag)
            .is_err()
    );
    assert!(guarded[1..n + 1].iter().all(|&b| b == 0));
    assert_eq!((guarded[0], guarded[n + 1]), (0xa5, 0xa5));
}

#[test]
fn aes_ocb_batch_boundaries() {
    let mut sizes: Vec<usize> = (0..=257).collect();
    for center in [512, 1024, 2048, 4096, 16384] {
        sizes.extend(center - 17..=center + 17);
    }
    for (key_len, cipher) in [
        (16, Cipher::aes_128_ocb()),
        (24, Cipher::aes_192_ocb()),
        (32, Cipher::aes_256_ocb()),
    ] {
        let key = vec![0x42; key_len];
        for &n in &sizes {
            compare::<8>(&key, cipher, n);
            compare::<12>(&key, cipher, n);
            compare::<16>(&key, cipher, n);
        }
    }
}
