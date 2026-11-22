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
use verified_garbage::ec::{self, P256, P384, P521};
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hashes::sha512::Sha512;
use verified_garbage::rsa::BigUint;
use verified_garbage::{ed25519, mldsa44, mldsa65, mldsa87, rsa};
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
        // NO-COVERAGE-START
        // `PrivateKeyDer` is non-exhaustive, but has no other form.
        _ => Err(Error::General("unsupported private key format".into())),
        // NO-COVERAGE-END
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
            };
            let key = key.check()?;
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

// Signing, and an ML-DSA key's generation from its seed, fail only if the
// operating system's random number generator does, with negligible
// probability (a loop of the library's reaching its bound), or, for RSA,
// with a modulus too short for the hash, which no key that loads has: in
// no test.
// NO-COVERAGE-START
fn signing_failed<E>(_: E) -> Error {
    Error::General("signing failed".into())
}

fn rsa_signing_failed(e: impl fmt::Display) -> Error {
    Error::General(alloc::format!("signing failed: {e}"))
}

fn mldsa_keygen_failed() -> Error {
    Error::General("ML-DSA key generation failed".into())
}
// NO-COVERAGE-END

/// A `SigningKey` for RSA-PKCS1 or RSA-PSS.
pub(crate) struct RsaSigningKey {
    key: Arc<rsa::PrivateKey>,
    /// The DER `RSAPublicKey`.
    public_key: Vec<u8>,
}

impl RsaSigningKey {
    /// The schemes it signs with, best first, each with whether it is PSS
    /// (or else PKCS #1 v1.5) and its hash.
    const SCHEMES: &[(SignatureScheme, bool, Hash)] = &[
        (SignatureScheme::RSA_PSS_SHA512, true, Hash::Sha512),
        (SignatureScheme::RSA_PSS_SHA384, true, Hash::Sha384),
        (SignatureScheme::RSA_PSS_SHA256, true, Hash::Sha256),
        (SignatureScheme::RSA_PKCS1_SHA512, false, Hash::Sha512),
        (SignatureScheme::RSA_PKCS1_SHA384, false, Hash::Sha384),
        (SignatureScheme::RSA_PKCS1_SHA256, false, Hash::Sha256),
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
        fn b<'a>(x: &asn1::BigUint<'a>) -> BigUint<'a> {
            BigUint::from_be_bytes(der::trim(x.as_bytes()))
        }
        let key = rsa::PrivateKey::from_crt(
            BigUint::from_be_bytes(n),
            b(&k.e),
            b(&k.d),
            b(&k.p),
            b(&k.q),
            b(&k.dp),
            b(&k.dq),
            b(&k.qinv),
        )
        .map_err(|e| Error::General(alloc::format!("failed to load RSA private key: {e}")))?;
        let public_key = der::RsaPublicKey { n: k.n, e: k.e }.to_der();
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
            .find(|(scheme, ..)| offered.contains(scheme))
            .map(|&(scheme, pss, hash)| {
                Box::new(RsaSigner {
                    key: self.key.clone(),
                    scheme,
                    pss,
                    hash,
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
    /// Whether `scheme` is PSS, or else PKCS #1 v1.5.
    pss: bool,
    /// The hash of `scheme`.
    hash: Hash,
}

impl Signer for RsaSigner {
    fn sign(self: Box<Self>, message: &[u8]) -> Result<Vec<u8>, Error> {
        let hash = self.hash;
        let digest = hash.digest(message);
        let digest = &digest[..hash.len()];
        match self.pss {
            // RFC 8446 §4.2.3: "The length of the Salt MUST be equal to the
            // length of the output of the digest algorithm."
            true => self
                .key
                .sign_pss(digest, hash.pss(), hash.pss(), hash.len())
                .map_err(rsa_signing_failed),
            false => self
                .key
                .sign_pkcs1v15(digest, hash.pkcs1())
                .map_err(rsa_signing_failed),
        }
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
    P256(ec::PrivateKey<P256>, [u8; 65]),
    P384(ec::PrivateKey<P384>, [u8; 97]),
    P521(ec::PrivateKey<P521>, [u8; 133]),
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
            make: impl FnOnce(&[u8; N]) -> Option<(ec::PrivateKey<C>, [u8; P])>,
        ) -> Result<(ec::PrivateKey<C>, [u8; P]), Error>
        where
            C: ec::Curve,
        {
            // RFC 5915 §3: the private key is exactly ceiling(log2(n)/8)
            // bytes long.
            let d = Zeroizing::new(<[u8; N]>::try_from(d).map_err(|_| bad_key("EC private key"))?);
            let (key, q) = make(&d).ok_or_else(|| bad_key("EC private key"))?;
            if public_key.is_some_and(|pk| pk != q) {
                return Err(bad_key("EC private key (public key mismatch)"));
            }
            Ok((key, q))
        }

        let (key, scheme) = match curve {
            der::SECP256R1 => {
                let (k, q) = load(k.private_key, public_key, |d| {
                    let key = ec::PrivateKey::<P256>::from_bytes(d);
                    let q = *key.public_key().ok()?.as_bytes();
                    Some((key, q))
                })?;
                (EcdsaKey::P256(k, q), SignatureScheme::ECDSA_NISTP256_SHA256)
            }
            der::SECP384R1 => {
                let (k, q) = load(k.private_key, public_key, |d| {
                    let key = ec::PrivateKey::<P384>::from_bytes(d);
                    let q = *key.public_key().ok()?.as_bytes();
                    Some((key, q))
                })?;
                (EcdsaKey::P384(k, q), SignatureScheme::ECDSA_NISTP384_SHA384)
            }
            der::SECP521R1 => {
                let (k, q) = load(k.private_key, public_key, |d| {
                    let key = ec::PrivateKey::<P521>::from_bytes(d);
                    let q = *key.public_key().ok()?.as_bytes();
                    Some((key, q))
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
        Ok(match &*self.key {
            EcdsaKey::P256(k, _) => {
                der::ecdsa_sig_to_der(&k.sign::<Sha256>(message).map_err(signing_failed)?)
            }
            EcdsaKey::P384(k, _) => {
                der::ecdsa_sig_to_der(&k.sign::<Sha384>(message).map_err(signing_failed)?)
            }
            EcdsaKey::P521(k, _) => {
                der::ecdsa_sig_to_der(&k.sign::<Sha512>(message).map_err(signing_failed)?)
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
        Ok(match self {
            Self::MlDsa44(k) => MlDsaKey::MlDsa44(k.ok_or_else(mldsa_keygen_failed)?),
            Self::MlDsa65(k) => MlDsaKey::MlDsa65(k.ok_or_else(mldsa_keygen_failed)?),
            Self::MlDsa87(k) => MlDsaKey::MlDsa87(k.ok_or_else(mldsa_keygen_failed)?),
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
        Ok(match &*self.0 {
            MlDsaKey::MlDsa44(k) => k.sign(message, &[]).map_err(signing_failed)?.to_vec(),
            MlDsaKey::MlDsa65(k) => k.sign(message, &[]).map_err(signing_failed)?.to_vec(),
            MlDsaKey::MlDsa87(k) => k.sign(message, &[]).map_err(signing_failed)?.to_vec(),
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

#[cfg(test)]
mod tests {
    use alloc::format;
    use alloc::vec::Vec;
    use std::sync::LazyLock;

    use pki_types::{
        PrivateKeyDer, PrivatePkcs1KeyDer, PrivatePkcs8KeyDer, PrivateSec1KeyDer,
        SignatureVerificationAlgorithm,
    };
    use rustls::crypto::{SignatureScheme, SigningKey, public_key_to_spki};
    use rustls::error::Error;
    use verified_garbage::ec::{self, P256, P384, P521};
    use verified_garbage::rsa::{self, BigUint};
    use verified_garbage::{ed25519, mldsa44, mldsa65, mldsa87};

    use super::load_private_key;
    use crate::verify::{
        RSA_PKCS1_2048_8192_SHA384, RSA_PKCS1_3072_8192_SHA384, SUPPORTED_SIG_ALGS,
    };
    use crate::{DEFAULT_KEY_PROVIDER, der};

    const MESSAGE: &[u8] = b"signed";

    /// The provider's verifier of `scheme` (the first it maps it to).
    fn verifier(scheme: SignatureScheme) -> &'static dyn SignatureVerificationAlgorithm {
        let (_, algs) = SUPPORTED_SIG_ALGS
            .mapping()
            .iter()
            .find(|(s, _)| *s == scheme)
            .unwrap();
        algs[0]
    }

    /// `key` signs with each of `schemes`, as the signer it chooses for that
    /// scheme alone, and the provider's verifier of the scheme accepts the
    /// signature with `public_key` (as the verifier takes it, which is what
    /// the key's SPKI holds), but not with the key or signature truncated, nor
    /// of another message. A key offered none of its schemes chooses none,
    /// and its debug form leaves out the key.
    fn signs(key: &dyn SigningKey, public_key: &[u8], schemes: &[SignatureScheme]) {
        assert!(format!("{key:?}").ends_with(".. }"));
        for &scheme in schemes {
            let signer = key.choose_scheme(&[scheme]).unwrap();
            assert_eq!(signer.scheme(), scheme);
            assert!(format!("{signer:?}").contains(&format!("{scheme:?}")));
            let verifier = verifier(scheme);
            let spki = public_key_to_spki(&verifier.public_key_alg_id(), public_key);
            assert_eq!(key.public_key().unwrap(), spki);
            let sig = signer.sign(MESSAGE).unwrap();
            assert!(verifier.verify_signature(public_key, MESSAGE, &sig).is_ok());
            assert!(
                verifier
                    .verify_signature(public_key, b"other", &sig)
                    .is_err()
            );
            let (pk, sig_len) = (&public_key[1..], sig.len() - 1);
            assert!(verifier.verify_signature(pk, MESSAGE, &sig).is_err());
            assert!(
                verifier
                    .verify_signature(public_key, MESSAGE, &sig[..sig_len])
                    .is_err()
            );
        }
        let none = [SignatureScheme::ECDSA_SHA1_Legacy];
        assert!(key.choose_scheme(&none).is_none());
    }

    /// The error of a key that does not load.
    fn fails(key: PrivateKeyDer<'_>) -> Error {
        load_private_key(&key).err().unwrap()
    }

    /// A bit string of the bytes `b`.
    fn bits(b: &[u8]) -> asn1::BitString<'_> {
        asn1::BitString::new(b, 0).unwrap()
    }

    /// A bit string whose last byte has an unused bit, which no public key
    /// is.
    fn unused_bit() -> asn1::BitString<'static> {
        asn1::BitString::new(&[0, 0], 1).unwrap()
    }

    /// A `OneAsymmetricKey` (PKCS #8, or with a public key RFC 5958's) of
    /// `version`, for the algorithm `oid` with the DER parameters `params`:
    /// its `AlgorithmIdentifier`, private key and, if any, `[1] IMPLICIT`
    /// public key.
    fn pkcs8(
        version: u8,
        oid: asn1::ObjectIdentifier,
        params: Option<&[u8]>,
        private_key: &[u8],
        public_key: Option<asn1::BitString<'_>>,
    ) -> PrivateKeyDer<'static> {
        let params = params.map(|p| asn1::parse_single::<asn1::Tlv<'_>>(p).unwrap());
        let public_key = public_key.map(asn1::Implicit::<_, 1>::new);
        let der = der::sequence(&|w| {
            w.write_element(&version)?;
            w.write_element(&asn1::SequenceWriter::new(&|w| {
                w.write_element(&oid)?;
                w.write_element(&params)
            }))?;
            w.write_element(&private_key)?;
            w.write_element(&public_key)
        });
        PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(der))
    }

    /// An `ECPrivateKey` (SEC 1) of `version`, the private key `d`, and, if
    /// any, the `[0] EXPLICIT` curve and `[1] EXPLICIT` public key.
    fn sec1(
        version: u8,
        d: &[u8],
        curve: Option<asn1::ObjectIdentifier>,
        public_key: Option<asn1::BitString<'_>>,
    ) -> Vec<u8> {
        let curve = curve.map(asn1::Explicit::<_, 0>::new);
        let public_key = public_key.map(asn1::Explicit::<_, 1>::new);
        der::sequence(&|w| {
            w.write_element(&version)?;
            w.write_element(&d)?;
            w.write_element(&curve)?;
            w.write_element(&public_key)
        })
    }

    /// The DER of a NULL, RSA keys' parameters.
    fn null() -> Vec<u8> {
        asn1::write_single(&()).unwrap()
    }

    /// The DER of the OID `oid`, EC keys' parameters.
    fn oid(oid: &asn1::ObjectIdentifier) -> Vec<u8> {
        asn1::write_single(oid).unwrap()
    }

    /// A 2048-bit RSA key from the library's key generation, made once.
    static RSA_KEY: LazyLock<rsa::PrivateKey> =
        LazyLock::new(|| rsa::keygen::generate(2048, BigUint::from_be_bytes(&[1, 0, 1])).unwrap());

    /// `RSA_KEY`'s `RSAPrivateKey`, after `edit`, and its `RSAPublicKey`.
    fn rsa_key(edit: impl FnOnce(&mut der::RsaPrivateKey<'_>)) -> (Vec<u8>, Vec<u8>) {
        let ints = RSA_KEY.components().map(|x| der::der_uint(x.as_be_bytes()));
        let [n, e, d, p, q, dp, dq, qinv] = ints.each_ref().map(|x| asn1::BigUint::new(x).unwrap());
        let mut key = der::RsaPrivateKey {
            version: 0,
            n,
            e,
            d,
            p,
            q,
            dp,
            dq,
            qinv,
        };
        edit(&mut key);
        let private_key = der::sequence(&|w| {
            w.write_element(&key.version)?;
            let k = &key;
            for x in [k.n, k.e, k.d, k.p, k.q, k.dp, k.dq, k.qinv] {
                w.write_element(&x)?;
            }
            Ok(())
        });
        let public_key = der::RsaPublicKey { n: key.n, e: key.e }.to_der();
        (private_key, public_key)
    }

    /// An RSA key loads as PKCS #1, and as PKCS #8 with its parameters NULL
    /// or absent, and signs with every RSA scheme; a PKCS #1 v1.5 signature
    /// with SHA-384 does not verify where the modulus must be 3072 bits.
    #[test]
    fn rsa_signs() {
        let (pkcs1, public_key) = rsa_key(|_| {});
        let schemes = [
            SignatureScheme::RSA_PSS_SHA256,
            SignatureScheme::RSA_PSS_SHA384,
            SignatureScheme::RSA_PSS_SHA512,
            SignatureScheme::RSA_PKCS1_SHA256,
            SignatureScheme::RSA_PKCS1_SHA384,
            SignatureScheme::RSA_PKCS1_SHA512,
        ];
        let null: &[u8] = &null();
        for der in [
            PrivateKeyDer::Pkcs1(PrivatePkcs1KeyDer::from(pkcs1.clone())),
            pkcs8(0, der::RSA_ENCRYPTION, Some(null), &pkcs1, None),
            pkcs8(0, der::RSA_ENCRYPTION, None, &pkcs1, None),
        ] {
            signs(&*load_private_key(&der).unwrap(), &public_key, &schemes);
        }
        let key = load_private_key(&PrivateKeyDer::Pkcs1(pkcs1.into())).unwrap();
        let sig = key
            .choose_scheme(&[SignatureScheme::RSA_PKCS1_SHA384])
            .unwrap()
            .sign(MESSAGE)
            .unwrap();
        assert!(
            RSA_PKCS1_2048_8192_SHA384
                .verify_signature(&public_key, MESSAGE, &sig)
                .is_ok()
        );
        assert!(
            RSA_PKCS1_3072_8192_SHA384
                .verify_signature(&public_key, MESSAGE, &sig)
                .is_err()
        );
    }

    /// An RSA key does not load if it is no `RSAPrivateKey`, has more than
    /// two primes (version 1), a modulus shorter than 2048 bits, values that
    /// are not one key's (a CRT coefficient that is not q's inverse modulo
    /// p), or, in PKCS #8, parameters other than NULL or a version above 1.
    #[test]
    fn rsa_rejects() {
        let pkcs1 = |der: Vec<u8>| PrivateKeyDer::Pkcs1(PrivatePkcs1KeyDer::from(der));
        let (key, _) = rsa_key(|_| {});
        let (multi_prime, _) = rsa_key(|k| k.version = 1);
        let (short, _) = rsa_key(|k| k.n = k.e);
        let (inconsistent, _) = rsa_key(|k| k.qinv = k.dp);
        fails(pkcs1(key[..key.len() - 1].to_vec()));
        fails(pkcs1(multi_prime));
        fails(pkcs1(short));
        fails(pkcs1(inconsistent));
        let curve: &[u8] = &oid(&der::SECP256R1);
        fails(pkcs8(0, der::RSA_ENCRYPTION, Some(curve), &key, None));
        fails(pkcs8(2, der::RSA_ENCRYPTION, None, &key, None));
    }

    /// An ECDSA key of each curve loads as SEC 1 with its curve (and its
    /// public key or not), and as PKCS #8 with the curve in either or both,
    /// and signs with its curve's scheme; it does not load with another
    /// version than 1, another curve in PKCS #8 than in SEC 1, no curve, a
    /// public key that is not its own (or a bit string with unused bits), a
    /// private key of another length or
    /// out of range, or a curve the provider does not have, and not if it
    /// is no `ECPrivateKey`.
    #[test]
    fn ecdsa() {
        macro_rules! check {
            ($curve:ty, $n:literal, $oid:expr, $other:expr, $scheme:expr) => {{
                // A scalar below each curve's order: its top byte zero.
                let mut d = [7u8; $n];
                d[0] = 0;
                let q = *ec::PrivateKey::<$curve>::from_bytes(&d)
                    .public_key()
                    .unwrap()
                    .as_bytes();
                let sec1_der = |der: Vec<u8>| PrivateKeyDer::Sec1(PrivateSec1KeyDer::from(der));
                let ec = |curve: Option<&[u8]>, sec1: &[u8]| {
                    pkcs8(0, der::EC_PUBLIC_KEY, curve, sec1, None)
                };
                let curve: &[u8] = &oid(&$oid);
                for der in [
                    sec1_der(sec1(1, &d, Some($oid), Some(bits(&q)))),
                    sec1_der(sec1(1, &d, Some($oid), None)),
                    ec(Some(curve), &sec1(1, &d, None, Some(bits(&q)))),
                    ec(Some(curve), &sec1(1, &d, Some($oid), None)),
                ] {
                    signs(&*load_private_key(&der).unwrap(), &q, &[$scheme]);
                }
                let other: &[u8] = &oid(&$other);
                let mut other_q = q;
                other_q[$n] ^= 1;
                let too_large = [0xff; $n];
                fails(sec1_der(sec1(0, &d, Some($oid), None)));
                fails(ec(Some(other), &sec1(1, &d, Some($oid), None)));
                fails(sec1_der(sec1(1, &d, None, None)));
                fails(sec1_der(sec1(1, &d, Some($oid), Some(bits(&other_q)))));
                fails(sec1_der(sec1(1, &d, Some($oid), Some(unused_bit()))));
                fails(sec1_der(sec1(1, &d[1..], Some($oid), None)));
                fails(sec1_der(sec1(1, &too_large, Some($oid), None)));
                fails(ec(Some(curve), &sec1(1, &d, Some($oid), None)[1..]));
                fails(ec(None, &sec1(1, &d, None, None)));
                // Ed25519's OID, which names no curve of ECDSA.
                fails(sec1_der(sec1(1, &d, Some(der::ED25519), None)));
            }};
        }
        check!(
            P256,
            32,
            der::SECP256R1,
            der::SECP384R1,
            SignatureScheme::ECDSA_NISTP256_SHA256
        );
        check!(
            P384,
            48,
            der::SECP384R1,
            der::SECP521R1,
            SignatureScheme::ECDSA_NISTP384_SHA384
        );
        check!(
            P521,
            66,
            der::SECP521R1,
            der::SECP256R1,
            SignatureScheme::ECDSA_NISTP521_SHA512
        );
    }

    /// An Ed25519 seed loads as PKCS #8 (through the provider's key
    /// provider), with its public key or none, and signs; it does not load
    /// with another public key (or a bit string with unused bits),
    /// parameters, or a seed of another length.
    #[test]
    fn ed25519() {
        let seed = [7u8; 32];
        let public_key = *ed25519::SigningKey::from_seed(&seed)
            .verifying_key()
            .as_bytes();
        let private_key = |seed: &[u8]| asn1::write_single(&seed).unwrap();
        for pk in [Some(bits(&public_key)), None] {
            let der = pkcs8(1, der::ED25519, None, &private_key(&seed), pk);
            let key = DEFAULT_KEY_PROVIDER.load_private_key(der).unwrap();
            signs(&*key, &public_key, &[SignatureScheme::ED25519]);
        }
        let mut other = public_key;
        other[0] ^= 1;
        let null: &[u8] = &null();
        let (sk, short) = (private_key(&seed), private_key(&seed[1..]));
        fails(pkcs8(1, der::ED25519, None, &sk, Some(bits(&other))));
        fails(pkcs8(1, der::ED25519, None, &sk, Some(unused_bit())));
        fails(pkcs8(0, der::ED25519, Some(null), &sk, None));
        fails(pkcs8(0, der::ED25519, None, &short, None));
    }

    /// The ML-DSA private key that is the seed `seed`, `[0] IMPLICIT`.
    fn mldsa_seed(seed: &[u8]) -> Vec<u8> {
        asn1::write_single(&asn1::Implicit::<_, 0>::new(seed)).unwrap()
    }

    /// The ML-DSA private key of both the seed `seed` and the expanded key
    /// `expanded`.
    fn mldsa_both(seed: &[u8], expanded: &[u8]) -> Vec<u8> {
        der::sequence(&|w| {
            w.write_element(&seed)?;
            w.write_element(&expanded)
        })
    }

    /// An ML-DSA seed of each parameter set loads as PKCS #8, alone or with
    /// its expanded key (which the provider does not read), with its public
    /// key or none, and signs; it does not load as the expanded key alone,
    /// with a seed of another length, another public key, or parameters.
    #[test]
    fn mldsa() {
        macro_rules! check {
            ($key:ty, $oid:expr, $scheme:expr) => {{
                let seed = [7u8; 32];
                let public_key = *<$key>::from_seed(&seed).unwrap().verifying_key().as_bytes();
                let mut other = public_key;
                other[0] ^= 1;
                let both = mldsa_both(&seed, &[1, 2, 3]);
                for der in [
                    pkcs8(0, $oid, None, &mldsa_seed(&seed), None),
                    pkcs8(1, $oid, None, &both, Some(bits(&public_key))),
                ] {
                    signs(&*load_private_key(&der).unwrap(), &public_key, &[$scheme]);
                }
                let null: &[u8] = &null();
                let expanded = asn1::write_single(&&[1u8, 2, 3][..]).unwrap();
                let short = mldsa_seed(&seed[1..]);
                let seed = mldsa_seed(&seed);
                fails(pkcs8(0, $oid, None, &expanded, None));
                fails(pkcs8(0, $oid, None, &short, None));
                fails(pkcs8(1, $oid, None, &seed, Some(bits(&other))));
                fails(pkcs8(0, $oid, Some(null), &seed, None));
            }};
        }
        check!(
            mldsa44::SigningKey44,
            der::ML_DSA_44,
            SignatureScheme::ML_DSA_44
        );
        check!(
            mldsa65::SigningKey65,
            der::ML_DSA_65,
            SignatureScheme::ML_DSA_65
        );
        check!(
            mldsa87::SigningKey87,
            der::ML_DSA_87,
            SignatureScheme::ML_DSA_87
        );
    }

    /// A PKCS #8 key does not load if it is not DER of one, or of an
    /// algorithm the provider does not sign with (P-256's OID, which names a
    /// curve, not a key's algorithm).
    #[test]
    fn pkcs8_rejects() {
        let seed = asn1::write_single(&&[7u8; 32][..]).unwrap();
        let err = fails(pkcs8(0, der::SECP256R1, None, &seed, None));
        assert!(format!("{err}").contains("failed to parse private key as"));
        fails(PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(seed)));
    }
}
