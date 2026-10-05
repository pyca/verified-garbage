use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use rustls::crypto::GetRandomFailed;
use rustls::crypto::kx::{
    ActiveKeyExchange, CompletedKeyExchange, Hybrid, HybridLayout, NamedGroup, SharedSecret,
    StartedKeyExchange, SupportedKxGroup,
};
use rustls::error::{Error, PeerMisbehaved};
use verified_garbage::ecdh::{self, P256, P384};
use verified_garbage::mlkem768::{DecapsulationKey768, EncapsulationKey768};
use verified_garbage::mlkem1024::{DecapsulationKey1024, EncapsulationKey1024};
use verified_garbage::x25519;
use zeroize::Zeroizing;

/// A list of the default key exchange groups supported by this provider.
///
/// This does not contain MLKEM768; by default MLKEM768 is only offered
/// in hybrid with X25519.
pub static DEFAULT_KX_GROUPS: &[&dyn SupportedKxGroup] =
    &[X25519MLKEM768, X25519, SECP256R1, SECP384R1];

/// A list of all the key exchange groups supported by this provider.
pub static ALL_KX_GROUPS: &[&dyn SupportedKxGroup] = &[
    X25519MLKEM768,
    SECP256R1MLKEM768,
    X25519,
    SECP256R1,
    SECP384R1,
    MLKEM768,
    MLKEM1024,
];

/// This is the [X25519MLKEM768] key exchange.
///
/// [X25519MLKEM768]: <https://datatracker.ietf.org/doc/draft-ietf-tls-ecdhe-mlkem/>
pub static X25519MLKEM768: &dyn SupportedKxGroup = &Hybrid {
    classical: X25519,
    post_quantum: MLKEM768,
    name: NamedGroup::X25519MLKEM768,
    layout: HybridLayout {
        classical_share_len: X25519_LEN,
        post_quantum_client_share_len: MLKEM768_ENCAP_LEN,
        post_quantum_server_share_len: MLKEM768_CIPHERTEXT_LEN,
        post_quantum_first: true,
    },
};

/// This is the [SECP256R1MLKEM768] key exchange.
///
/// [SECP256R1MLKEM768]: <https://datatracker.ietf.org/doc/draft-ietf-tls-ecdhe-mlkem/>
pub static SECP256R1MLKEM768: &dyn SupportedKxGroup = &Hybrid {
    classical: SECP256R1,
    post_quantum: MLKEM768,
    name: NamedGroup::secp256r1MLKEM768,
    layout: HybridLayout {
        classical_share_len: SECP256R1_LEN,
        post_quantum_client_share_len: MLKEM768_ENCAP_LEN,
        post_quantum_server_share_len: MLKEM768_CIPHERTEXT_LEN,
        post_quantum_first: false,
    },
};

/// This is the [MLKEM] key encapsulation mechanism in NIST with security category 3.
///
/// [MLKEM]: https://datatracker.ietf.org/doc/draft-ietf-tls-mlkem
pub static MLKEM768: &dyn SupportedKxGroup = &MlKem768;

/// This is the [MLKEM] key encapsulation mechanism in NIST with security category 5.
///
/// [MLKEM]: https://datatracker.ietf.org/doc/draft-ietf-tls-mlkem
pub static MLKEM1024: &dyn SupportedKxGroup = &MlKem1024;

/// Ephemeral ECDH on curve25519 (see RFC 7748)
pub static X25519: &dyn SupportedKxGroup = &X25519Group;

/// Ephemeral ECDH on secp256r1 (aka NIST-P256)
pub static SECP256R1: &dyn SupportedKxGroup = &Secp256r1;

/// Ephemeral ECDH on secp384r1 (aka NIST-P384)
pub static SECP384R1: &dyn SupportedKxGroup = &Secp384r1;

const X25519_LEN: usize = 32;
const SECP256R1_LEN: usize = 65;
const MLKEM768_CIPHERTEXT_LEN: usize = 1088;
const MLKEM768_ENCAP_LEN: usize = 1184;

fn random<const N: usize>() -> Result<Zeroizing<[u8; N]>, GetRandomFailed> {
    let mut bytes = Zeroizing::new([0u8; N]);
    getrandom::fill(&mut *bytes).map_err(|_| GetRandomFailed)?;
    Ok(bytes)
}

/// An in-progress key exchange: our private key and public key.
/// The peer's share is `PEER` bytes long.
struct KeyExchange<K, const PUB: usize, const PEER: usize> {
    group: NamedGroup,
    priv_key: K,
    pub_key: [u8; PUB],
    agree: fn(&K, &[u8; PEER]) -> Option<SharedSecret>,
}

impl<K: Send + Sync, const PUB: usize, const PEER: usize> ActiveKeyExchange
    for KeyExchange<K, PUB, PEER>
{
    fn complete(self: Box<Self>, peer: &[u8]) -> Result<SharedSecret, Error> {
        // For the NIST curves, both shares are uncompressed points (RFC 9846
        // §4.3.8.2), whose validity the verified ECDH checks.
        let peer = <&[u8; PEER]>::try_from(peer).map_err(|_| PeerMisbehaved::InvalidKeyShare)?;
        (self.agree)(&self.priv_key, peer).ok_or_else(|| PeerMisbehaved::InvalidKeyShare.into())
    }

    fn group(&self) -> NamedGroup {
        self.group
    }

    fn pub_key(&self) -> &[u8] {
        &self.pub_key
    }
}

struct X25519Group;

impl SupportedKxGroup for X25519Group {
    fn start(&self) -> Result<StartedKeyExchange, Error> {
        let priv_key = x25519::PrivateKey::generate().map_err(|_| GetRandomFailed)?;
        Ok(StartedKeyExchange::Single(Box::new(KeyExchange {
            group: NamedGroup::X25519,
            pub_key: priv_key.public_key(),
            priv_key,
            agree: |k, peer| {
                let shared = Zeroizing::new(k.diffie_hellman(peer).ok()?);
                Some(SharedSecret::from(&shared[..]))
            },
        })))
    }

    fn name(&self) -> NamedGroup {
        NamedGroup::X25519
    }
}

impl fmt::Debug for X25519Group {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        NamedGroup::X25519.fmt(f)
    }
}

/// Ephemeral ECDH on a NIST curve: `$len`-byte private keys and `$pub`-byte
/// uncompressed public keys.
macro_rules! nist_group {
    ($name:ident, $curve:ty, $group:expr, $len:literal, $pub:literal) => {
        struct $name;

        impl SupportedKxGroup for $name {
            fn start(&self) -> Result<StartedKeyExchange, Error> {
                // Rejection sampling (FIPS 186-5 §A.4.2): a candidate is a
                // private key if it is in [1, n − 1], which deriving its
                // public key checks.
                let (priv_key, pub_key) = loop {
                    let k = ecdh::PrivateKey::<$curve>::from_bytes(&*random::<$len>()?);
                    if let Ok(pub_key) = k.public_key() {
                        break (k, pub_key);
                    }
                };
                Ok(StartedKeyExchange::Single(Box::new(KeyExchange {
                    group: $group,
                    priv_key,
                    pub_key,
                    agree: |k, peer| {
                        let shared = Zeroizing::new(k.diffie_hellman(peer).ok()?);
                        Some(SharedSecret::from(&shared[..]))
                    },
                })))
            }

            fn name(&self) -> NamedGroup {
                $group
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                $group.fmt(f)
            }
        }
    };
}

nist_group!(Secp256r1, P256, NamedGroup::secp256r1, 32, 65);
nist_group!(Secp384r1, P384, NamedGroup::secp384r1, 48, 97);

/// ML-KEM as a key exchange (draft-ietf-tls-mlkem): the client's share is
/// an encapsulation key, and the server's a ciphertext to it.
macro_rules! ml_kem_group {
    ($name:ident, $dk:ident, $ek:ident, $group:expr) => {
        #[derive(Debug)]
        struct $name;

        impl SupportedKxGroup for $name {
            fn start(&self) -> Result<StartedKeyExchange, Error> {
                let decaps_key = $dk::from_seed(&*random::<64>()?)
                    .map_err(|_| Error::General("ML-KEM key generation failed".into()))?;
                Ok(StartedKeyExchange::Single(Box::new(KeyExchange {
                    group: $group,
                    pub_key: *decaps_key.encapsulation_key().as_bytes(),
                    priv_key: Box::new(decaps_key),
                    agree: |k, ct| {
                        let shared = Zeroizing::new(k.decapsulate(ct).ok()?);
                        Some(SharedSecret::from(&shared[..]))
                    },
                })))
            }

            fn start_and_complete(
                &self,
                client_share: &[u8],
            ) -> Result<CompletedKeyExchange, Error> {
                let client_share = client_share
                    .try_into()
                    .map_err(|_| PeerMisbehaved::InvalidKeyShare)?;
                let encaps_key =
                    $ek::from_bytes(client_share).map_err(|_| PeerMisbehaved::InvalidKeyShare)?;
                let (shared, ciphertext) = encaps_key
                    .encapsulate()
                    .map_err(|_| PeerMisbehaved::InvalidKeyShare)?;
                let shared = Zeroizing::new(shared);
                Ok(CompletedKeyExchange {
                    group: $group,
                    pub_key: Vec::from(ciphertext),
                    secret: SharedSecret::from(&shared[..]),
                })
            }

            fn name(&self) -> NamedGroup {
                $group
            }
        }
    };
}

ml_kem_group!(
    MlKem768,
    DecapsulationKey768,
    EncapsulationKey768,
    NamedGroup::MLKEM768
);
ml_kem_group!(
    MlKem1024,
    DecapsulationKey1024,
    EncapsulationKey1024,
    NamedGroup::MLKEM1024
);
