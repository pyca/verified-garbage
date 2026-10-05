//! HMAC with SHA-2: TLS 1.2's PRF and, through HKDF, TLS 1.3's key schedule.

use alloc::boxed::Box;

use rustls::crypto;
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hashes::sha512::Sha512;
use verified_garbage::hmac::{self, HmacHash};

pub(crate) static HMAC_SHA256: Hmac<Sha256> = Hmac(core::marker::PhantomData);
pub(crate) static HMAC_SHA384: Hmac<Sha384> = Hmac(core::marker::PhantomData);
#[allow(dead_code)] // HPKE's HKDF-SHA512 suites and the TLS 1.2 PRF test.
pub(crate) static HMAC_SHA512: Hmac<Sha512> = Hmac(core::marker::PhantomData);

pub(crate) struct Hmac<H>(core::marker::PhantomData<fn() -> H>);

impl<H: HmacHash + 'static> crypto::hmac::Hmac for Hmac<H>
where
    H::State: Send + Sync,
{
    fn with_key(&self, key: &[u8]) -> Box<dyn crypto::hmac::Key> {
        Box::new(Key(hmac::Hmac::<H>::new(key)))
    }

    fn hash_output_len(&self) -> usize {
        H::OUTPUT_SIZE
    }
}

/// An HMAC computation that has absorbed only the key: each MAC continues
/// a copy of it, so the key is processed once.
struct Key<H: HmacHash>(hmac::Hmac<H>);

impl<H: HmacHash> crypto::hmac::Key for Key<H>
where
    H::State: Send + Sync,
{
    fn sign_concat(&self, first: &[u8], middle: &[&[u8]], last: &[u8]) -> crypto::hmac::Tag {
        let mut h = self.0.clone();
        h.update(first);
        for m in middle {
            h.update(m);
        }
        h.update(last);
        crypto::hmac::Tag::new(h.finalize().as_ref())
    }

    fn tag_len(&self) -> usize {
        H::OUTPUT_SIZE
    }
}
