//! HKDF (RFC 5869) with SHA-2, for TLS 1.3's key schedule, directly on the
//! library's HMAC. rustls's generic `HkdfUsingHmac` boxes a keyed HMAC and
//! allocates the PRK for every extract; here an extract computes the PRK in
//! place and boxes only the expander, which keeps the PRK as a keyed HMAC.

use alloc::boxed::Box;
use core::marker::PhantomData;

use rustls::crypto::hmac::Tag;
use rustls::crypto::tls13::{self, HkdfExpander, OkmBlock, OutputLengthError};
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hmac::{Hmac, HmacHash};

pub(crate) static HKDF_SHA256: Hkdf<Sha256> = Hkdf(PhantomData);
pub(crate) static HKDF_SHA384: Hkdf<Sha384> = Hkdf(PhantomData);

pub(crate) struct Hkdf<H>(PhantomData<fn() -> H>);

impl<H: HmacHash + 'static> Hkdf<H>
where
    H::State: Send + Sync,
{
    /// `HKDF-Extract(salt, secret)`, as an expander; no salt is `HashLen`
    /// zero bytes.
    fn extract(salt: Option<&[u8]>, secret: &[u8]) -> Box<dyn HkdfExpander> {
        let zeroes = [0u8; Tag::MAX_LEN];
        let mut h = Hmac::<H>::new(salt.unwrap_or(&zeroes[..H::OUTPUT_SIZE]));
        h.update(secret);
        Box::new(Expander(Hmac::<H>::new(h.finalize().as_ref())))
    }
}

impl<H: HmacHash + 'static> tls13::Hkdf for Hkdf<H>
where
    H::State: Send + Sync,
{
    fn extract_from_zero_ikm(&self, salt: Option<&[u8]>) -> Box<dyn HkdfExpander> {
        Self::extract(salt, &[0u8; Tag::MAX_LEN][..H::OUTPUT_SIZE])
    }

    fn extract_from_secret(&self, salt: Option<&[u8]>, secret: &[u8]) -> Box<dyn HkdfExpander> {
        Self::extract(salt, secret)
    }

    fn expander_for_okm(&self, okm: &OkmBlock) -> Box<dyn HkdfExpander> {
        Box::new(Expander(Hmac::<H>::new(okm.as_ref())))
    }

    fn hmac_sign(&self, key: &OkmBlock, message: &[u8]) -> Tag {
        Tag::new(Hmac::<H>::mac(key.as_ref(), message).as_ref())
    }
}

/// `HKDF-Expand` with the PRK absorbed as an HMAC key: each output block
/// continues a copy of it.
struct Expander<H: HmacHash>(Hmac<H>);

impl<H: HmacHash> Expander<H> {
    /// `T(1) ‖ T(2) ‖ …` into `output`, where
    /// `T(i) = HMAC(PRK, T(i - 1) ‖ info ‖ i)` and `T(0)` is empty.
    fn expand(&self, info: &[&[u8]], output: &mut [u8]) {
        let mut prev: Option<H::Output> = None;
        for (i, block) in output.chunks_mut(H::OUTPUT_SIZE).enumerate() {
            let mut h = self.0.clone();
            if let Some(t) = &prev {
                h.update(t.as_ref());
            }
            for piece in info {
                h.update(piece);
            }
            // At most 255 blocks (`expand_slice` checks it).
            h.update(&[i as u8 + 1]);
            let t = h.finalize();
            block.copy_from_slice(&t.as_ref()[..block.len()]);
            prev = Some(t);
        }
    }
}

impl<H: HmacHash> HkdfExpander for Expander<H>
where
    H::State: Send + Sync,
{
    fn expand_slice(&self, info: &[&[u8]], output: &mut [u8]) -> Result<(), OutputLengthError> {
        if output.len() > 255 * H::OUTPUT_SIZE {
            return Err(OutputLengthError);
        }
        self.expand(info, output);
        Ok(())
    }

    fn expand_block(&self, info: &[&[u8]]) -> OkmBlock {
        let mut block = [0u8; Tag::MAX_LEN];
        self.expand(info, &mut block[..H::OUTPUT_SIZE]);
        OkmBlock::new(&block[..H::OUTPUT_SIZE])
    }

    fn hash_len(&self) -> usize {
        H::OUTPUT_SIZE
    }
}
