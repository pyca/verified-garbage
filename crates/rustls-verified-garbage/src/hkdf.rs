//! HKDF (RFC 5869) with SHA-2, for TLS 1.3's key schedule: the library's
//! verified HKDF ([`verified_garbage::kdf::hkdf`]). An expander holds the
//! pseudorandom key as HMAC keyed with it, so each expansion starts from the
//! keyed states rather than keying HMAC again.
//!
//! A pseudorandom key shorter than a digest, which RFC 5869 does not allow
//! and the library refuses, but which rustls's trait takes (its key schedule
//! never gives one), is expanded by rustls's own HKDF over the verified HMAC
//! (`HkdfUsingHmac`), as aws-lc-rs's provider and rustls's generic HKDF
//! accept one.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::marker::PhantomData;

use rustls::crypto::hmac;
use rustls::crypto::hmac::Tag;
use rustls::crypto::tls13::{self, HkdfExpander, HkdfUsingHmac, OkmBlock, OutputLengthError};
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hmac::{Hmac, HmacHash};
use verified_garbage::kdf::hkdf::{Hkdf as VgHkdf, HkdfHash};

pub(crate) static HKDF_SHA256: Hkdf<Sha256> = Hkdf(PhantomData, &crate::hmac::HMAC_SHA256);
pub(crate) static HKDF_SHA384: Hkdf<Sha384> = Hkdf(PhantomData, &crate::hmac::HMAC_SHA384);

/// HKDF over `H`, with the verified HMAC over `H` for a pseudorandom key
/// shorter than a digest.
pub(crate) struct Hkdf<H>(PhantomData<fn() -> H>, &'static dyn hmac::Hmac);

impl<H: HkdfHash + HmacHash + Send + Sync + 'static> tls13::Hkdf for Hkdf<H> {
    fn extract_from_zero_ikm(&self, salt: Option<&[u8]>) -> Box<dyn HkdfExpander> {
        let zeroes = [0u8; Tag::MAX_LEN];
        Box::new(Expander(VgHkdf::<H>::new(salt, &zeroes[..H::OUTPUT_SIZE])))
    }

    fn extract_from_secret(&self, salt: Option<&[u8]>, secret: &[u8]) -> Box<dyn HkdfExpander> {
        Box::new(Expander(VgHkdf::<H>::new(salt, secret)))
    }

    fn expander_for_okm(&self, okm: &OkmBlock) -> Box<dyn HkdfExpander> {
        match VgHkdf::<H>::from_prk(okm.as_ref()) {
            Ok(prk) => Box::new(Expander(prk)),
            // Shorter than a digest (see the module's documentation).
            Err(_) => HkdfUsingHmac(self.1).expander_for_okm(okm),
        }
    }

    fn hmac_sign(&self, key: &OkmBlock, message: &[u8]) -> Tag {
        Tag::new(Hmac::<H>::mac(key.as_ref(), message).as_ref())
    }
}

/// The longest `info` TLS 1.3 asks for, an `HkdfLabel` (RFC 8446 §7.1): a
/// length, a label of up to 255 bytes and a context of up to 255, each of
/// the last two after its length byte.
const MAX_LABEL: usize = 2 + 1 + 255 + 1 + 255;

/// HKDF-Expand from a pseudorandom key.
struct Expander<H: HkdfHash>(VgHkdf<H>);

impl<H: HkdfHash> Expander<H> {
    /// HKDF-Expand of `info`'s pieces, one after the other, into `output`,
    /// at most 255 digests long.
    fn expand(&self, info: &[&[u8]], output: &mut [u8]) {
        let len: usize = info.iter().map(|p| p.len()).sum();
        let mut stack = [0u8; MAX_LABEL];
        let mut heap = Vec::new();
        let buf = if len <= MAX_LABEL {
            &mut stack[..len]
        } else {
            heap.resize(len, 0);
            &mut heap[..]
        };
        let mut at = 0;
        for piece in info {
            buf[at..at + piece.len()].copy_from_slice(piece);
            at += piece.len();
        }
        self.0
            .expand(buf, output)
            .expect("the output is at most 255 digests long");
    }
}

impl<H: HkdfHash + Send + Sync> HkdfExpander for Expander<H> {
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
