//! Private keys loaded from DER, and signing with them.

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt::{self, Debug, Formatter};

use pki_types::{
    AlgorithmIdentifier, PrivateKeyDer, PrivatePkcs8KeyDer, SubjectPublicKeyInfoDer, alg_id,
};
use rustls::crypto::{SignatureScheme, Signer, SigningKey, public_key_to_spki};
use rustls::error::Error;
use verified_garbage::ecdsa::{self, P256, P384, P521};
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hashes::sha512::Sha512;
use verified_garbage::{ed25519, mldsa44, mldsa65, mldsa87, rsa, rsa_pkcs1_sig, rsa_pss};
use zeroize::Zeroizing;

use crate::der;
use crate::verify::Hash;

/// Loads `key_der` as any key type this provider signs with.
pub(crate) fn load_private_key(key_der: &PrivateKeyDer<'_>) -> Result<Box<dyn SigningKey>, Error> {
    match key_der {
        PrivateKeyDer::Pkcs1(pkcs1) => Ok(Box::new(RsaSigningKey::from_pkcs1(
            pkcs1.secret_pkcs1_der(),
        )?)),
        PrivateKeyDer::Sec1(sec1) => Ok(Box::new(EcdsaSigner::from_sec1(
            sec1.secret_sec1_der(),
            None,
        )?)),
        PrivateKeyDer::Pkcs8(pkcs8) => load_pkcs8(pkcs8),
        _ => Err(Error::General("unsupported private key format".into())),
    }
}

fn load_pkcs8(pkcs8: &PrivatePkcs8KeyDer<'_>) -> Result<Box<dyn SigningKey>, Error> {
    let key = asn1::parse_single::<der::OneAsymmetricKey<'_>>(pkcs8.secret_pkcs8_der())
        .map_err(|_| Error::General("failed to parse PKCS#8 private key".into()))?;
    if key.version > 1 {
        return Err(Error::General("unsupported PKCS#8 version".into()));
    }
    let params = key.algorithm.params;
    let public_key = key
        .public_key
        .as_ref()
        .map(|b| der::bit_string_bytes(b).ok_or_else(|| bad_key("PKCS#8 public key")))
        .transpose()?;
    match key.algorithm.oid {
        der::RSA_ENCRYPTION => {
            // The parameters are NULL (RFC 8017 §A.1), which some encoders
            // leave out.
            if params.is_some_and(|p| p.full_data() != [0x05, 0x00]) {
                return Err(bad_key("RSA key parameters"));
            }
            Ok(Box::new(RsaSigningKey::from_pkcs1(key.private_key)?))
        }
        der::EC_PUBLIC_KEY => {
            let curve = params
                .and_then(|p| p.parse::<asn1::ObjectIdentifier>().ok())
                .ok_or_else(|| bad_key("EC key parameters"))?;
            Ok(Box::new(EcdsaSigner::from_sec1(
                key.private_key,
                Some(&curve),
            )?))
        }
        der::ED25519 if params.is_none() => {
            let seed = asn1::parse_single::<&[u8]>(key.private_key)
                .ok()
                .and_then(|s| <&[u8; 32]>::try_from(s).ok())
                .ok_or_else(|| bad_key("Ed25519 key"))?;
            let key = ed25519::SigningKey::from_seed(seed);
            if public_key.is_some_and(|pk| pk != key.verifying_key().as_bytes()) {
                return Err(bad_key("Ed25519 key (public key mismatch)"));
            }
            Ok(Box::new(Ed25519Signer(Arc::new(key))))
        }
        oid @ (der::ML_DSA_44 | der::ML_DSA_65 | der::ML_DSA_87) if params.is_none() => {
            let seed = match asn1::parse_single::<der::MlDsaPrivateKey<'_>>(key.private_key) {
                Ok(der::MlDsaPrivateKey::Seed(seed)) => seed,
                Ok(der::MlDsaPrivateKey::Both(both)) => both.seed,
                // A key without its seed cannot be loaded: verified-garbage
                // keeps ML-DSA keys as seeds.
                _ => return Err(bad_key("ML-DSA key (only seeds are supported)")),
            };
            let seed = <&[u8; 32]>::try_from(seed).map_err(|_| bad_key("ML-DSA seed"))?;
            let key = match oid {
                der::ML_DSA_44 => MlDsaKey::MlDsa44(mldsa44::SigningKey44::from_seed(seed).ok()),
                der::ML_DSA_65 => MlDsaKey::MlDsa65(mldsa65::SigningKey65::from_seed(seed).ok()),
                _ => MlDsaKey::MlDsa87(mldsa87::SigningKey87::from_seed(seed).ok()),
            }
            .check()?;
            if public_key.is_some_and(|pk| pk != key.public_key()) {
                return Err(bad_key("ML-DSA key (public key mismatch)"));
            }
            Ok(Box::new(MlDsaSigner(Arc::new(key))))
        }
        _ => Err(Error::General(
            "failed to parse private key as RSA, ECDSA, EdDSA or ML-DSA".into(),
        )),
    }
}

fn bad_key(what: &str) -> Error {
    Error::General(alloc::format!("invalid {what}"))
}

/// A `SigningKey` for RSA-PKCS1 or RSA-PSS.
pub(crate) struct RsaSigningKey {
    key: Arc<rsa::PrivateKey>,
    /// The DER `RSAPublicKey`.
    public_key: Vec<u8>,
}

impl RsaSigningKey {
    const SCHEMES: &[SignatureScheme] = &[
        SignatureScheme::RSA_PSS_SHA512,
        SignatureScheme::RSA_PSS_SHA384,
        SignatureScheme::RSA_PSS_SHA256,
        SignatureScheme::RSA_PKCS1_SHA512,
        SignatureScheme::RSA_PKCS1_SHA384,
        SignatureScheme::RSA_PKCS1_SHA256,
    ];

    /// The key of a DER `RSAPrivateKey` (PKCS #1).
    fn from_pkcs1(der: &[u8]) -> Result<Self, Error> {
        let k = asn1::parse_single::<der::RsaPrivateKey<'_>>(der)
            .map_err(|_| bad_key("RSA private key"))?;
        if k.version != 0 {
            return Err(bad_key("RSA private key (multi-prime)"));
        }
        let n = der::trim(k.n.as_bytes());
        // As aws-lc-rs requires: 2048 to 8192 bits.
        if !(2048 / 8..=8192 / 8).contains(&n.len()) {
            return Err(bad_key("RSA private key (size)"));
        }
        let key = rsa::PrivateKey::from_crt(
            n,
            k.e.as_bytes(),
            k.d.as_bytes(),
            k.p.as_bytes(),
            k.q.as_bytes(),
            k.dp.as_bytes(),
            k.dq.as_bytes(),
            k.qinv.as_bytes(),
        )
        .map_err(|e| Error::General(alloc::format!("failed to load RSA private key: {e}")))?;
        let public_key = asn1::write_single(&der::RsaPublicKey { n: k.n, e: k.e }).unwrap();
        Ok(Self {
            key: Arc::new(key),
            public_key,
        })
    }
}

impl SigningKey for RsaSigningKey {
    fn choose_scheme(&self, offered: &[SignatureScheme]) -> Option<Box<dyn Signer>> {
        Self::SCHEMES
            .iter()
            .find(|scheme| offered.contains(scheme))
            .map(|&scheme| {
                Box::new(RsaSigner {
                    key: self.key.clone(),
                    scheme,
                }) as Box<dyn Signer>
            })
    }

    fn public_key(&self) -> Option<SubjectPublicKeyInfoDer<'_>> {
        Some(public_key_to_spki(
            &alg_id::RSA_ENCRYPTION,
            &self.public_key,
        ))
    }
}

impl Debug for RsaSigningKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("RsaSigningKey").finish_non_exhaustive()
    }
}

struct RsaSigner {
    key: Arc<rsa::PrivateKey>,
    scheme: SignatureScheme,
}

impl Signer for RsaSigner {
    fn sign(self: Box<Self>, message: &[u8]) -> Result<Vec<u8>, Error> {
        let (pss, hash) = match self.scheme {
            SignatureScheme::RSA_PKCS1_SHA256 => (false, Hash::Sha256),
            SignatureScheme::RSA_PKCS1_SHA384 => (false, Hash::Sha384),
            SignatureScheme::RSA_PKCS1_SHA512 => (false, Hash::Sha512),
            SignatureScheme::RSA_PSS_SHA256 => (true, Hash::Sha256),
            SignatureScheme::RSA_PSS_SHA384 => (true, Hash::Sha384),
            SignatureScheme::RSA_PSS_SHA512 => (true, Hash::Sha512),
            _ => unreachable!(),
        };
        let digest = hash.digest(message);
        let digest = &digest[..hash.len()];
        let sig = match pss {
            // RFC 8446 §4.2.3: "The length of the Salt MUST be equal to the
            // length of the output of the digest algorithm."
            true => rsa_pss::sign(&self.key, digest, hash.pss(), hash.pss(), hash.len())
                .map_err(|e| Error::General(alloc::format!("signing failed: {e}"))),
            false => rsa_pkcs1_sig::sign(&self.key, digest, hash.pkcs1())
                .map_err(|e| Error::General(alloc::format!("signing failed: {e}"))),
        }?;
        Ok(sig)
    }

    fn scheme(&self) -> SignatureScheme {
        self.scheme
    }
}

impl Debug for RsaSigner {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("RsaSigner")
            .field("scheme", &self.scheme)
            .finish_non_exhaustive()
    }
}

/// An ECDSA private key on one of the NIST curves.
enum EcdsaKey {
    P256(ecdsa::SigningKey<P256>, [u8; 65]),
    P384(ecdsa::SigningKey<P384>, [u8; 97]),
    P521(ecdsa::SigningKey<P521>, [u8; 133]),
}

/// A [`SigningKey`] and [`Signer`] implementation for ECDSA.
///
/// Each key signs with exactly one scheme: its curve's, with the hash of
/// its size.
#[derive(Clone)]
pub(crate) struct EcdsaSigner {
    key: Arc<EcdsaKey>,
    scheme: SignatureScheme,
}

impl EcdsaSigner {
    /// The key of a DER `ECPrivateKey` (SEC 1), on the curve `curve` (from
    /// PKCS #8) or its own parameters.
    fn from_sec1(der: &[u8], curve: Option<&asn1::ObjectIdentifier>) -> Result<Self, Error> {
        let k = asn1::parse_single::<der::EcPrivateKey<'_>>(der)
            .map_err(|_| bad_key("EC private key"))?;
        if k.version != 1 {
            return Err(bad_key("EC private key version"));
        }
        let curve = match (curve, &k.parameters) {
            (Some(c), Some(p)) if c != p => return Err(bad_key("EC private key parameters")),
            (Some(c), _) | (None, Some(c)) => c.clone(),
            (None, None) => return Err(bad_key("EC private key (no curve)")),
        };
        let public_key = k
            .public_key
            .as_ref()
            .map(|b| der::bit_string_bytes(b).ok_or_else(|| bad_key("EC public key")))
            .transpose()?;

        fn load<C, const N: usize, const P: usize>(
            d: &[u8],
            public_key: Option<&[u8]>,
            make: impl FnOnce(&[u8; N]) -> Result<(ecdsa::SigningKey<C>, [u8; P]), ecdsa::Error>,
        ) -> Result<(ecdsa::SigningKey<C>, [u8; P]), Error>
        where
            C: ecdsa::Curve,
        {
            // RFC 5915 §3: the private key is exactly ceiling(log2(n)/8)
            // bytes long.
            let d = Zeroizing::new(<[u8; N]>::try_from(d).map_err(|_| bad_key("EC private key"))?);
            let (key, q) = make(&d).map_err(|_| bad_key("EC private key"))?;
            if public_key.is_some_and(|pk| pk != q) {
                return Err(bad_key("EC private key (public key mismatch)"));
            }
            Ok((key, q))
        }

        let (key, scheme) = match curve {
            der::SECP256R1 => {
                let (k, q) = load(k.private_key, public_key, |d| {
                    let key = ecdsa::SigningKey::<P256>::from_bytes(d);
                    key.public_key().map(|q| (key, q))
                })?;
                (EcdsaKey::P256(k, q), SignatureScheme::ECDSA_NISTP256_SHA256)
            }
            der::SECP384R1 => {
                let (k, q) = load(k.private_key, public_key, |d| {
                    let key = ecdsa::SigningKey::<P384>::from_bytes(d);
                    key.public_key().map(|q| (key, q))
                })?;
                (EcdsaKey::P384(k, q), SignatureScheme::ECDSA_NISTP384_SHA384)
            }
            der::SECP521R1 => {
                let (k, q) = load(k.private_key, public_key, |d| {
                    let key = ecdsa::SigningKey::<P521>::from_bytes(d);
                    key.public_key().map(|q| (key, q))
                })?;
                (EcdsaKey::P521(k, q), SignatureScheme::ECDSA_NISTP521_SHA512)
            }
            _ => return Err(bad_key("EC private key (unsupported curve)")),
        };
        Ok(Self {
            key: Arc::new(key),
            scheme,
        })
    }
}

impl SigningKey for EcdsaSigner {
    fn choose_scheme(&self, offered: &[SignatureScheme]) -> Option<Box<dyn Signer>> {
        if offered.contains(&self.scheme) {
            Some(Box::new(self.clone()))
        } else {
            None
        }
    }

    fn public_key(&self) -> Option<SubjectPublicKeyInfoDer<'_>> {
        Some(match &*self.key {
            EcdsaKey::P256(_, q) => public_key_to_spki(&alg_id::ECDSA_P256, q),
            EcdsaKey::P384(_, q) => public_key_to_spki(&alg_id::ECDSA_P384, q),
            EcdsaKey::P521(_, q) => public_key_to_spki(&alg_id::ECDSA_P521, q),
        })
    }
}

impl Signer for EcdsaSigner {
    fn sign(self: Box<Self>, message: &[u8]) -> Result<Vec<u8>, Error> {
        let failed = |_| Error::General("signing failed".into());
        Ok(match &*self.key {
            EcdsaKey::P256(k, _) => {
                der::ecdsa_sig_to_der(&k.sign::<Sha256>(message).map_err(failed)?)
            }
            EcdsaKey::P384(k, _) => {
                der::ecdsa_sig_to_der(&k.sign::<Sha384>(message).map_err(failed)?)
            }
            EcdsaKey::P521(k, _) => {
                der::ecdsa_sig_to_der(&k.sign::<Sha512>(message).map_err(failed)?)
            }
        })
    }

    fn scheme(&self) -> SignatureScheme {
        self.scheme
    }
}

impl Debug for EcdsaSigner {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("EcdsaSigner")
            .field("scheme", &self.scheme)
            .finish_non_exhaustive()
    }
}

/// A [`SigningKey`] and [`Signer`] implementation for Ed25519.
#[derive(Clone)]
pub(crate) struct Ed25519Signer(Arc<ed25519::SigningKey>);

impl SigningKey for Ed25519Signer {
    fn choose_scheme(&self, offered: &[SignatureScheme]) -> Option<Box<dyn Signer>> {
        if offered.contains(&SignatureScheme::ED25519) {
            Some(Box::new(self.clone()))
        } else {
            None
        }
    }

    fn public_key(&self) -> Option<SubjectPublicKeyInfoDer<'_>> {
        Some(public_key_to_spki(
            &alg_id::ED25519,
            self.0.verifying_key().as_bytes(),
        ))
    }
}

impl Signer for Ed25519Signer {
    fn sign(self: Box<Self>, message: &[u8]) -> Result<Vec<u8>, Error> {
        Ok(self.0.sign(message).to_vec())
    }

    fn scheme(&self) -> SignatureScheme {
        SignatureScheme::ED25519
    }
}

impl Debug for Ed25519Signer {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ed25519Signer")
            .field("scheme", &SignatureScheme::ED25519)
            .finish_non_exhaustive()
    }
}

/// An ML-DSA private key, or `None` if its key generation failed (with
/// negligible probability).
enum MlDsaKey<A, B, C> {
    MlDsa44(A),
    MlDsa65(B),
    MlDsa87(C),
}

type MlDsaLoaded = MlDsaKey<mldsa44::SigningKey44, mldsa65::SigningKey65, mldsa87::SigningKey87>;

impl
    MlDsaKey<
        Option<mldsa44::SigningKey44>,
        Option<mldsa65::SigningKey65>,
        Option<mldsa87::SigningKey87>,
    >
{
    fn check(self) -> Result<MlDsaLoaded, Error> {
        let failed = || Error::General("ML-DSA key generation failed".into());
        Ok(match self {
            Self::MlDsa44(k) => MlDsaKey::MlDsa44(k.ok_or_else(failed)?),
            Self::MlDsa65(k) => MlDsaKey::MlDsa65(k.ok_or_else(failed)?),
            Self::MlDsa87(k) => MlDsaKey::MlDsa87(k.ok_or_else(failed)?),
        })
    }
}

impl MlDsaLoaded {
    fn public_key(&self) -> &[u8] {
        match self {
            Self::MlDsa44(k) => k.verifying_key().as_bytes(),
            Self::MlDsa65(k) => k.verifying_key().as_bytes(),
            Self::MlDsa87(k) => k.verifying_key().as_bytes(),
        }
    }

    fn scheme(&self) -> SignatureScheme {
        match self {
            Self::MlDsa44(_) => SignatureScheme::ML_DSA_44,
            Self::MlDsa65(_) => SignatureScheme::ML_DSA_65,
            Self::MlDsa87(_) => SignatureScheme::ML_DSA_87,
        }
    }

    fn alg_id(&self) -> AlgorithmIdentifier {
        match self {
            Self::MlDsa44(_) => alg_id::ML_DSA_44,
            Self::MlDsa65(_) => alg_id::ML_DSA_65,
            Self::MlDsa87(_) => alg_id::ML_DSA_87,
        }
    }
}

/// A [`SigningKey`] and [`Signer`] implementation for ML-DSA.
#[derive(Clone)]
pub(crate) struct MlDsaSigner(Arc<MlDsaLoaded>);

impl SigningKey for MlDsaSigner {
    fn choose_scheme(&self, offered: &[SignatureScheme]) -> Option<Box<dyn Signer>> {
        if offered.contains(&self.0.scheme()) {
            Some(Box::new(self.clone()))
        } else {
            None
        }
    }

    fn public_key(&self) -> Option<SubjectPublicKeyInfoDer<'_>> {
        Some(public_key_to_spki(&self.0.alg_id(), self.0.public_key()))
    }
}

impl Signer for MlDsaSigner {
    fn sign(self: Box<Self>, message: &[u8]) -> Result<Vec<u8>, Error> {
        fn failed<E>(_: E) -> Error {
            Error::General("signing failed".into())
        }
        Ok(match &*self.0 {
            MlDsaKey::MlDsa44(k) => k.sign(message, &[]).map_err(failed)?.to_vec(),
            MlDsaKey::MlDsa65(k) => k.sign(message, &[]).map_err(failed)?.to_vec(),
            MlDsaKey::MlDsa87(k) => k.sign(message, &[]).map_err(failed)?.to_vec(),
        })
    }

    fn scheme(&self) -> SignatureScheme {
        self.0.scheme()
    }
}

impl Debug for MlDsaSigner {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("MlDsaSigner")
            .field("scheme", &self.0.scheme())
            .finish_non_exhaustive()
    }
}
