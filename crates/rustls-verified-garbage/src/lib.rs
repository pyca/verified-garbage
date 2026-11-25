//! A rustls [`CryptoProvider`] whose cryptography is verified-garbage's:
//! formally verified assembly, generated from Lean.
//!
//! It offers what rustls' aws-lc-rs provider does: TLS 1.2 and 1.3 with
//! AES-GCM and ChaCha20-Poly1305; X25519, P-256, P-384, ML-KEM and the
//! X25519MLKEM768 and SECP256R1MLKEM768 hybrids; signatures with RSA
//! (PKCS #1 v1.5 and PSS), ECDSA (P-256, P-384, P-521), Ed25519 and ML-DSA;
//! session tickets; and QUIC's packet and header protection. Keys are read
//! with rust-asn1. HPKE (for ECH) is not provided.
//!
//! Use it like:
//!
//! ```
//! # use std::sync::Arc;
//! # use rustls::{ClientConfig, RootCertStore};
//! # let roots = RootCertStore::empty();
//! let config = ClientConfig::builder(Arc::new(rustls_verified_garbage::DEFAULT_PROVIDER))
//!     .with_root_certificates(roots)
//!     .with_no_client_auth();
//! ```
//!
//! To offer other suites or groups, replace [`DEFAULT_PROVIDER`]'s with those
//! of [`cipher_suite`] or [`kx_group`].

#![no_std]
#![warn(missing_docs)]

extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::sync::Arc;
#[cfg(feature = "std")]
use core::time::Duration;

use pki_types::PrivateKeyDer;
use rustls::crypto::{
    CryptoProvider, GetRandomFailed, KeyProvider, SecureRandom, SigningKey, TicketProducer,
    TicketerFactory,
};
use rustls::error::Error;
#[cfg(feature = "std")]
use rustls::ticketer::TicketRotator;

mod aead;
mod der;
mod hash;
mod hkdf;
mod hmac;
mod kx;
mod quic;
mod sign;
#[cfg(feature = "std")]
mod ticketer;
mod tls12;
mod tls13;
mod verify;

pub use verify::ALL_VERIFICATION_ALGS;

/// The default `CryptoProvider` backed by verified-garbage.
pub const DEFAULT_PROVIDER: CryptoProvider = CryptoProvider {
    tls12_cipher_suites: Cow::Borrowed(tls12::ALL_TLS12_CIPHER_SUITES),
    tls13_cipher_suites: Cow::Borrowed(tls13::ALL_TLS13_CIPHER_SUITES),
    kx_groups: Cow::Borrowed(kx::DEFAULT_KX_GROUPS),
    signature_verification_algorithms: verify::SUPPORTED_SIG_ALGS,
    secure_random: &VerifiedGarbage,
    key_provider: &VerifiedGarbage,
    ticketer_factory: &VerifiedGarbage,
};

/// The default `CryptoProvider` backed by verified-garbage that only
/// supports TLS1.3.
pub const DEFAULT_TLS13_PROVIDER: CryptoProvider = CryptoProvider {
    tls12_cipher_suites: Cow::Borrowed(&[]),
    ..DEFAULT_PROVIDER
};

/// The default `CryptoProvider` backed by verified-garbage that only
/// supports TLS1.2.
///
/// Use of TLS1.3 is **strongly** recommended.
pub const DEFAULT_TLS12_PROVIDER: CryptoProvider = CryptoProvider {
    tls13_cipher_suites: Cow::Borrowed(&[]),
    ..DEFAULT_PROVIDER
};

#[derive(Debug)]
struct VerifiedGarbage;

impl SecureRandom for VerifiedGarbage {
    fn fill(&self, buf: &mut [u8]) -> Result<(), GetRandomFailed> {
        // verified-garbage draws its own randomness (keys, nonces, salts)
        // from the operating system, as this does.
        getrandom::fill(buf).map_err(|_| GetRandomFailed)
    }
}

impl KeyProvider for VerifiedGarbage {
    fn load_private_key(
        &self,
        key_der: PrivateKeyDer<'static>,
    ) -> Result<Box<dyn SigningKey>, Error> {
        let key_der = zeroize::Zeroizing::new(key_der);
        sign::load_private_key(&key_der)
    }
}

impl TicketerFactory for VerifiedGarbage {
    /// Make the recommended `Ticketer`.
    ///
    /// This produces tickets:
    ///
    /// - where each lasts for at least 6 hours,
    /// - with randomly generated keys, and
    /// - where keys are rotated every 6 hours.
    ///
    /// The encryption mechanism used is AES-256-GCM.
    fn ticketer(&self) -> Result<Arc<dyn TicketProducer>, Error> {
        #[cfg(feature = "std")]
        {
            let rotator = TicketRotator::new(SIX_HOURS, ticketer::AeadTicketer::new)?;
            Ok(Arc::new(rotator))
        }
        #[cfg(not(feature = "std"))]
        {
            Err(Error::General(
                "VerifiedGarbage::ticketer() relies on std-only RwLock via TicketRotator".into(),
            ))
        }
    }
}

#[cfg(feature = "std")]
const SIX_HOURS: Duration = Duration::from_secs(6 * 60 * 60);

/// The cipher suites this provider supports.
///
/// [`DEFAULT_PROVIDER`] offers all of them.
pub mod cipher_suite {
    pub use super::tls12::{
        ALL_TLS12_CIPHER_SUITES, TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
        TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384, TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256,
        TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256, TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
        TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256,
    };
    pub use super::tls13::{
        ALL_TLS13_CIPHER_SUITES, TLS13_AES_128_GCM_SHA256, TLS13_AES_256_GCM_SHA384,
        TLS13_CHACHA20_POLY1305_SHA256,
    };
}

/// The key exchange groups this provider supports.
///
/// The default providers offer [`X25519MLKEM768`](kx_group::X25519MLKEM768),
/// [`X25519`](kx_group::X25519), [`SECP256R1`](kx_group::SECP256R1) and
/// [`SECP384R1`](kx_group::SECP384R1), in that order of preference.
pub mod kx_group {
    pub use super::kx::{
        ALL_KX_GROUPS, MLKEM768, MLKEM1024, SECP256R1, SECP256R1MLKEM768, SECP384R1, X25519,
        X25519MLKEM768,
    };
}
