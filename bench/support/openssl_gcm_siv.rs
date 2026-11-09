//! OpenSSL's one-shot GCM-SIV API, with in-place data and a separate tag.
use openssl::{cipher::CipherRef, cipher_ctx::CipherCtx, error::ErrorStack};

pub fn seal(
    cipher: &CipherRef,
    key: &[u8],
    nonce: &[u8; 12],
    aad: &[u8],
    data: &mut [u8],
) -> [u8; 16] {
    let mut ctx = CipherCtx::new().unwrap();
    ctx.encrypt_init(Some(cipher), Some(key), Some(nonce))
        .unwrap();
    if !aad.is_empty() {
        ctx.cipher_update(aad, None).unwrap();
    }
    assert_eq!(
        ctx.cipher_update_inplace(data, data.len()).unwrap(),
        data.len()
    );
    assert_eq!(ctx.cipher_final(&mut []).unwrap(), 0);
    let mut tag = [0; 16];
    ctx.tag(&mut tag).unwrap();
    tag
}

pub fn open(
    cipher: &CipherRef,
    key: &[u8],
    nonce: &[u8; 12],
    aad: &[u8],
    data: &mut [u8],
    tag: &[u8; 16],
) -> Result<(), ErrorStack> {
    let mut ctx = CipherCtx::new()?;
    ctx.decrypt_init(Some(cipher), Some(key), Some(nonce))?;
    ctx.set_tag(tag)?;
    if !aad.is_empty() {
        ctx.cipher_update(aad, None)?;
    }
    assert_eq!(ctx.cipher_update_inplace(data, data.len())?, data.len());
    assert_eq!(ctx.cipher_final(&mut [])?, 0);
    Ok(())
}
