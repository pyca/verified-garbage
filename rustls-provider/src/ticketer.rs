use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;
use core::fmt::{Debug, Formatter};
use core::sync::atomic::{AtomicUsize, Ordering};
use core::time::Duration;

use rustls::crypto::{GetRandomFailed, TicketProducer};
use rustls::error::Error;
use subtle::ConstantTimeEq;
use verified_garbage::aes_gcm::AesGcm;
use zeroize::Zeroizing;

use crate::aead::TAG_LEN;

const NONCE_LEN: usize = 12;

/// A [`TicketProducer`] that encrypts tickets with AES-256-GCM.
///
/// It does not enforce any lifetime constraint.
pub(super) struct AeadTicketer {
    key: AesGcm,
    key_name: [u8; 16],

    /// Tracks the largest ciphertext produced by `encrypt`, and
    /// uses it to early-reject `decrypt` queries that are too long.
    ///
    /// Accepting excessively long ciphertexts means a "Partitioning
    /// Oracle Attack" (see <https://eprint.iacr.org/2020/1491.pdf>)
    /// can be more efficient, though also note that these are thought
    /// to be cryptographically hard if the key is full-entropy (as it
    /// is here).
    maximum_ciphertext_len: AtomicUsize,
}

impl AeadTicketer {
    #[allow(clippy::new_ret_no_self)]
    pub(super) fn new() -> Result<Box<dyn TicketProducer>, Error> {
        let mut key = Zeroizing::new([0u8; 32]);
        getrandom::fill(&mut *key).map_err(|_| GetRandomFailed)?;

        let mut key_name = [0u8; 16];
        getrandom::fill(&mut key_name).map_err(|_| GetRandomFailed)?;

        Ok(Box::new(Self {
            key: AesGcm::new(&*key).unwrap(),
            key_name,
            maximum_ciphertext_len: AtomicUsize::new(0),
        }))
    }
}

impl TicketProducer for AeadTicketer {
    /// Encrypt `message` and return the ciphertext.
    fn encrypt(&self, message: &[u8]) -> Option<Vec<u8>> {
        // Random nonce, because a counter is a privacy leak.
        let mut nonce = [0u8; NONCE_LEN];
        getrandom::fill(&mut nonce).ok()?;

        // ciphertext structure is:
        // key_name: [u8; 16]
        // nonce: [u8; 12]
        // message: [u8, _]
        // tag: [u8; 16]

        let mut ciphertext =
            Vec::with_capacity(self.key_name.len() + nonce.len() + message.len() + TAG_LEN);
        ciphertext.extend(self.key_name);
        ciphertext.extend(nonce);
        ciphertext.extend(message);
        let tag = self
            .key
            .encrypt_in_place(
                &nonce,
                &self.key_name,
                &mut ciphertext[self.key_name.len() + NONCE_LEN..],
            )
            .ok()?;
        ciphertext.extend(tag);

        self.maximum_ciphertext_len
            .fetch_max(ciphertext.len(), Ordering::SeqCst);
        Some(ciphertext)
    }

    /// Decrypt `ciphertext` and recover the original message.
    fn decrypt(&self, ciphertext: &[u8]) -> Option<Vec<u8>> {
        if ciphertext.len() > self.maximum_ciphertext_len.load(Ordering::SeqCst) {
            return None;
        }

        let (alleged_key_name, ciphertext) = ciphertext.split_at_checked(self.key_name.len())?;
        let (nonce, ciphertext) = ciphertext.split_at_checked(NONCE_LEN)?;
        let (ciphertext, tag) =
            ciphertext.split_at_checked(ciphertext.len().checked_sub(TAG_LEN)?)?;

        // checking the key_name is the expected one, *and* then putting it into the
        // additionally authenticated data is duplicative.  this check quickly rejects
        // tickets for a different ticketer (see `TicketRotator`), while including it
        // in the AAD ensures it is authenticated independent of that check and that
        // any attempted attack on the integrity such as [^1] must happen for each
        // `key_label`, not over a population of potential keys.  this approach
        // is overall similar to [^2].
        //
        // [^1]: https://eprint.iacr.org/2020/1491.pdf
        // [^2]: "Authenticated Encryption with Key Identification", fig 6
        //       <https://eprint.iacr.org/2022/1680.pdf>
        if ConstantTimeEq::ct_ne(&self.key_name[..], alleged_key_name).into() {
            return None;
        }

        let mut out = Vec::from(ciphertext);
        self.key
            .decrypt_in_place(nonce, alleged_key_name, &mut out, tag.try_into().ok()?)
            .ok()?;
        Some(out)
    }

    fn lifetime(&self) -> Duration {
        // this is not used, as this ticketer is only used via a `TicketRotator`
        // that is responsible for defining and managing the lifetime of tickets.
        Duration::ZERO
    }
}

impl Debug for AeadTicketer {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Note: we deliberately omit the key from the debug output.
        f.debug_struct("AeadTicketer").finish_non_exhaustive()
    }
}
