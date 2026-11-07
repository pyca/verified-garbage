//! Signature verification for webpki (certificates) and rustls (handshake
//! signatures).

use pki_types::{AlgorithmIdentifier, InvalidSignature, SignatureVerificationAlgorithm, alg_id};
use rustls::crypto::{SignatureScheme, WebPkiSupportedAlgorithms};
use verified_garbage::ecdsa::{P256, P384, P521, VerifyingKey};
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::hashes::sha384::Sha384;
use verified_garbage::hashes::sha512::Sha512;
use verified_garbage::{ed25519, mldsa44, mldsa65, mldsa87, rsa, rsa_pkcs1_sig, rsa_pss};

use crate::der;

/// A `WebPkiSupportedAlgorithms` value that reflects this provider's
/// capabilities.
pub static SUPPORTED_SIG_ALGS: WebPkiSupportedAlgorithms = match WebPkiSupportedAlgorithms::new(
    &[
        ECDSA_P256_SHA256,
        ECDSA_P256_SHA384,
        ECDSA_P256_SHA512,
        ECDSA_P384_SHA256,
        ECDSA_P384_SHA384,
        ECDSA_P384_SHA512,
        ECDSA_P521_SHA256,
        ECDSA_P521_SHA384,
        ECDSA_P521_SHA512,
        ED25519,
        RSA_PSS_2048_8192_SHA256_LEGACY_KEY,
        RSA_PSS_2048_8192_SHA384_LEGACY_KEY,
        RSA_PSS_2048_8192_SHA512_LEGACY_KEY,
        RSA_PKCS1_2048_8192_SHA256,
        RSA_PKCS1_2048_8192_SHA384,
        RSA_PKCS1_2048_8192_SHA512,
        RSA_PKCS1_2048_8192_SHA256_ABSENT_PARAMS,
        RSA_PKCS1_2048_8192_SHA384_ABSENT_PARAMS,
        RSA_PKCS1_2048_8192_SHA512_ABSENT_PARAMS,
        ML_DSA_44,
        ML_DSA_65,
        ML_DSA_87,
    ],
    &[
        // Note: for TLS1.2 the curve is not fixed by SignatureScheme. For TLS1.3 it is.
        (
            SignatureScheme::ECDSA_NISTP384_SHA384,
            &[ECDSA_P384_SHA384, ECDSA_P256_SHA384, ECDSA_P521_SHA384],
        ),
        (
            SignatureScheme::ECDSA_NISTP256_SHA256,
            &[ECDSA_P256_SHA256, ECDSA_P384_SHA256, ECDSA_P521_SHA256],
        ),
        (
            SignatureScheme::ECDSA_NISTP521_SHA512,
            &[ECDSA_P521_SHA512, ECDSA_P384_SHA512, ECDSA_P256_SHA512],
        ),
        (SignatureScheme::ED25519, &[ED25519]),
        (
            SignatureScheme::RSA_PSS_SHA512,
            &[RSA_PSS_2048_8192_SHA512_LEGACY_KEY],
        ),
        (
            SignatureScheme::RSA_PSS_SHA384,
            &[RSA_PSS_2048_8192_SHA384_LEGACY_KEY],
        ),
        (
            SignatureScheme::RSA_PSS_SHA256,
            &[RSA_PSS_2048_8192_SHA256_LEGACY_KEY],
        ),
        (
            SignatureScheme::RSA_PKCS1_SHA512,
            &[RSA_PKCS1_2048_8192_SHA512],
        ),
        (
            SignatureScheme::RSA_PKCS1_SHA384,
            &[RSA_PKCS1_2048_8192_SHA384],
        ),
        (
            SignatureScheme::RSA_PKCS1_SHA256,
            &[RSA_PKCS1_2048_8192_SHA256],
        ),
        (SignatureScheme::ML_DSA_44, &[ML_DSA_44]),
        (SignatureScheme::ML_DSA_65, &[ML_DSA_65]),
        (SignatureScheme::ML_DSA_87, &[ML_DSA_87]),
    ],
) {
    Ok(algs) => algs,
    Err(_) => panic!("bad WebPkiSupportedAlgorithms"),
};

/// An array of all the verification algorithms exported by this crate.
pub static ALL_VERIFICATION_ALGS: &[&dyn SignatureVerificationAlgorithm] = &[
    ECDSA_P256_SHA256,
    ECDSA_P256_SHA384,
    ECDSA_P256_SHA512,
    ECDSA_P384_SHA256,
    ECDSA_P384_SHA384,
    ECDSA_P384_SHA512,
    ECDSA_P521_SHA256,
    ECDSA_P521_SHA384,
    ECDSA_P521_SHA512,
    ED25519,
    RSA_PKCS1_2048_8192_SHA256,
    RSA_PKCS1_2048_8192_SHA384,
    RSA_PKCS1_2048_8192_SHA512,
    RSA_PKCS1_2048_8192_SHA256_ABSENT_PARAMS,
    RSA_PKCS1_2048_8192_SHA384_ABSENT_PARAMS,
    RSA_PKCS1_2048_8192_SHA512_ABSENT_PARAMS,
    RSA_PKCS1_3072_8192_SHA384,
    RSA_PSS_2048_8192_SHA256_LEGACY_KEY,
    RSA_PSS_2048_8192_SHA384_LEGACY_KEY,
    RSA_PSS_2048_8192_SHA512_LEGACY_KEY,
    ML_DSA_44,
    ML_DSA_65,
    ML_DSA_87,
];

/// A hash function of a signature algorithm.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Hash {
    Sha256,
    Sha384,
    Sha512,
}

impl Hash {
    /// The digest of `message`, in the first `len()` bytes.
    pub(crate) fn digest(self, message: &[u8]) -> [u8; 64] {
        let mut out = [0u8; 64];
        match self {
            Self::Sha256 => out[..32].copy_from_slice(&Sha256::digest(message)),
            Self::Sha384 => out[..48].copy_from_slice(&Sha384::digest(message)),
            Self::Sha512 => out.copy_from_slice(&Sha512::digest(message)),
        }
        out
    }

    pub(crate) fn len(self) -> usize {
        match self {
            Self::Sha256 => 32,
            Self::Sha384 => 48,
            Self::Sha512 => 64,
        }
    }

    pub(crate) fn pkcs1(self) -> rsa_pkcs1_sig::Hash {
        match self {
            Self::Sha256 => rsa_pkcs1_sig::Hash::Sha256,
            Self::Sha384 => rsa_pkcs1_sig::Hash::Sha384,
            Self::Sha512 => rsa_pkcs1_sig::Hash::Sha512,
        }
    }

    pub(crate) fn pss(self) -> rsa_pss::Hash {
        match self {
            Self::Sha256 => rsa_pss::Hash::Sha256,
            Self::Sha384 => rsa_pss::Hash::Sha384,
            Self::Sha512 => rsa_pss::Hash::Sha512,
        }
    }
}

/// A curve of ECDSA signatures.
#[derive(Clone, Copy, Debug)]
enum Curve {
    P256,
    P384,
    P521,
}

/// How a [`VerificationAlgorithm`] verifies.
#[derive(Debug)]
enum Kind {
    Ecdsa(Curve, Hash),
    Ed25519,
    /// RSASSA-PKCS1-v1_5, with a modulus of at least this many bytes.
    RsaPkcs1(Hash, usize),
    /// RSASSA-PSS with MGF1 over the same hash, and a salt as long as the
    /// hash (RFC 8446 §4.2.3).
    RsaPss(Hash),
    MlDsa44,
    MlDsa65,
    MlDsa87,
}

/// A `SignatureVerificationAlgorithm` implemented with verified-garbage.
#[derive(Debug)]
pub struct VerificationAlgorithm {
    public_key_alg_id: AlgorithmIdentifier,
    signature_alg_id: AlgorithmIdentifier,
    kind: Kind,
}

impl SignatureVerificationAlgorithm for VerificationAlgorithm {
    fn public_key_alg_id(&self) -> AlgorithmIdentifier {
        self.public_key_alg_id
    }

    fn signature_alg_id(&self) -> AlgorithmIdentifier {
        self.signature_alg_id
    }

    fn verify_signature(
        &self,
        public_key: &[u8],
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), InvalidSignature> {
        let ok = match self.kind {
            Kind::Ecdsa(curve, hash) => verify_ecdsa(curve, hash, public_key, message, signature),
            Kind::Ed25519 => verify_ed25519(public_key, message, signature),
            Kind::RsaPkcs1(hash, min_len) => {
                rsa_public_key(public_key, min_len).is_some_and(|key| {
                    let digest = hash.digest(message);
                    rsa_pkcs1_sig::verify(&key, signature, &digest[..hash.len()], hash.pkcs1())
                })
            }
            Kind::RsaPss(hash) => rsa_public_key(public_key, 2048 / 8).is_some_and(|key| {
                let digest = hash.digest(message);
                rsa_pss::verify(
                    &key,
                    signature,
                    &digest[..hash.len()],
                    hash.pss(),
                    hash.pss(),
                    rsa_pss::SaltLength::Len(hash.len()),
                )
            }),
            Kind::MlDsa44 => verify_mldsa(public_key, signature, |pk, sig| {
                mldsa44::VerifyingKey44::from_bytes(pk).verify(message, &[], sig)
            }),
            Kind::MlDsa65 => verify_mldsa(public_key, signature, |pk, sig| {
                mldsa65::VerifyingKey65::from_bytes(pk).verify(message, &[], sig)
            }),
            Kind::MlDsa87 => verify_mldsa(public_key, signature, |pk, sig| {
                mldsa87::VerifyingKey87::from_bytes(pk).verify(message, &[], sig)
            }),
        };
        match ok {
            true => Ok(()),
            false => Err(InvalidSignature),
        }
    }
}

/// The RSA public key of an `RSAPublicKey`, if its modulus is at least
/// `min_len` bytes (as ring and aws-lc-rs count it, rounding the bits up).
pub(crate) fn rsa_public_key(der: &[u8], min_len: usize) -> Option<rsa::PublicKey> {
    let key = asn1::parse_single::<der::RsaPublicKey<'_>>(der).ok()?;
    let n = der::trim(key.n.as_bytes());
    if n.len() < min_len {
        return None;
    }
    rsa::PublicKey::new(n, key.e.as_bytes()).ok()
}

/// `digest` as an `N`-byte `e` (FIPS 186-5 §6.4.2, for an order of `8 N`
/// bits): its leftmost `N` bytes, or all of it with leading zeros.
fn ecdsa_e<const N: usize>(digest: &[u8]) -> [u8; N] {
    let mut e = [0u8; N];
    if digest.len() >= N {
        e.copy_from_slice(&digest[..N]);
    } else {
        e[N - digest.len()..].copy_from_slice(digest);
    }
    e
}

fn verify_ecdsa(curve: Curve, hash: Hash, public_key: &[u8], message: &[u8], sig: &[u8]) -> bool {
    let digest = hash.digest(message);
    let digest = &digest[..hash.len()];
    // The verified function of each curve takes the hash value of its own
    // hash function, and uses as `e` its leftmost bits, as many as the
    // order has: for P-256 and P-384, exactly those of the hash value; for
    // P-521, all of SHA-512's. Given the `e` of another hash function (the
    // same computation), it verifies a signature of that hash function.
    match curve {
        Curve::P256 => {
            let (Ok(q), Some((r, s))) = (public_key.try_into(), der::ecdsa_sig_from_der::<32>(sig))
            else {
                return false;
            };
            VerifyingKey::<P256>::from_bytes(q)
                .verify_prehashed::<Sha256>(&ecdsa_e(digest), &concat(&r, &s))
                .is_ok()
        }
        Curve::P384 => {
            let (Ok(q), Some((r, s))) = (public_key.try_into(), der::ecdsa_sig_from_der::<48>(sig))
            else {
                return false;
            };
            VerifyingKey::<P384>::from_bytes(q)
                .verify_prehashed::<Sha384>(&ecdsa_e(digest), &concat(&r, &s))
                .is_ok()
        }
        Curve::P521 => {
            let (Ok(q), Some((r, s))) = (public_key.try_into(), der::ecdsa_sig_from_der::<66>(sig))
            else {
                return false;
            };
            VerifyingKey::<P521>::from_bytes(q)
                .verify_prehashed::<Sha512>(&ecdsa_e(digest), &concat(&r, &s))
                .is_ok()
        }
    }
}

/// `r ‖ s`.
fn concat<const N: usize, const M: usize>(r: &[u8; N], s: &[u8; N]) -> [u8; M] {
    let mut out = [0u8; M];
    out[..N].copy_from_slice(r);
    out[N..].copy_from_slice(s);
    out
}

fn verify_ed25519(public_key: &[u8], message: &[u8], signature: &[u8]) -> bool {
    let Ok(public_key) = public_key.try_into() else {
        return false;
    };
    ed25519::VerifyingKey::from_bytes(public_key)
        .verify(message, signature)
        .is_ok()
}

fn verify_mldsa<const PK: usize, const SIG: usize, E>(
    public_key: &[u8],
    signature: &[u8],
    verify: impl FnOnce(&[u8; PK], &[u8; SIG]) -> Result<(), E>,
) -> bool {
    match (public_key.try_into(), signature.try_into()) {
        (Ok(pk), Ok(sig)) => verify(pk, sig).is_ok(),
        _ => false,
    }
}

/// ECDSA signatures using the P-256 curve and SHA-256.
pub static ECDSA_P256_SHA256: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ECDSA_P256,
    signature_alg_id: alg_id::ECDSA_SHA256,
    kind: Kind::Ecdsa(Curve::P256, Hash::Sha256),
};

/// ECDSA signatures using the P-256 curve and SHA-384. Deprecated.
pub static ECDSA_P256_SHA384: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ECDSA_P256,
    signature_alg_id: alg_id::ECDSA_SHA384,
    kind: Kind::Ecdsa(Curve::P256, Hash::Sha384),
};

/// ECDSA signatures using the P-256 curve and SHA-512. Deprecated.
pub static ECDSA_P256_SHA512: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ECDSA_P256,
    signature_alg_id: alg_id::ECDSA_SHA512,
    kind: Kind::Ecdsa(Curve::P256, Hash::Sha512),
};

/// ECDSA signatures using the P-384 curve and SHA-256. Deprecated.
pub static ECDSA_P384_SHA256: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ECDSA_P384,
    signature_alg_id: alg_id::ECDSA_SHA256,
    kind: Kind::Ecdsa(Curve::P384, Hash::Sha256),
};

/// ECDSA signatures using the P-384 curve and SHA-384.
pub static ECDSA_P384_SHA384: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ECDSA_P384,
    signature_alg_id: alg_id::ECDSA_SHA384,
    kind: Kind::Ecdsa(Curve::P384, Hash::Sha384),
};

/// ECDSA signatures using the P-384 curve and SHA-512. Deprecated.
pub static ECDSA_P384_SHA512: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ECDSA_P384,
    signature_alg_id: alg_id::ECDSA_SHA512,
    kind: Kind::Ecdsa(Curve::P384, Hash::Sha512),
};

/// ECDSA signatures using the P-521 curve and SHA-256.
pub static ECDSA_P521_SHA256: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ECDSA_P521,
    signature_alg_id: alg_id::ECDSA_SHA256,
    kind: Kind::Ecdsa(Curve::P521, Hash::Sha256),
};

/// ECDSA signatures using the P-521 curve and SHA-384.
pub static ECDSA_P521_SHA384: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ECDSA_P521,
    signature_alg_id: alg_id::ECDSA_SHA384,
    kind: Kind::Ecdsa(Curve::P521, Hash::Sha384),
};

/// ECDSA signatures using the P-521 curve and SHA-512.
pub static ECDSA_P521_SHA512: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ECDSA_P521,
    signature_alg_id: alg_id::ECDSA_SHA512,
    kind: Kind::Ecdsa(Curve::P521, Hash::Sha512),
};

/// RSA PKCS#1 1.5 signatures using SHA-256 for keys of 2048-8192 bits.
pub static RSA_PKCS1_2048_8192_SHA256: &dyn SignatureVerificationAlgorithm =
    &VerificationAlgorithm {
        public_key_alg_id: alg_id::RSA_ENCRYPTION,
        signature_alg_id: alg_id::RSA_PKCS1_SHA256,
        kind: Kind::RsaPkcs1(Hash::Sha256, 2048 / 8),
    };

/// RSA PKCS#1 1.5 signatures using SHA-384 for keys of 2048-8192 bits.
pub static RSA_PKCS1_2048_8192_SHA384: &dyn SignatureVerificationAlgorithm =
    &VerificationAlgorithm {
        public_key_alg_id: alg_id::RSA_ENCRYPTION,
        signature_alg_id: alg_id::RSA_PKCS1_SHA384,
        kind: Kind::RsaPkcs1(Hash::Sha384, 2048 / 8),
    };

/// RSA PKCS#1 1.5 signatures using SHA-512 for keys of 2048-8192 bits.
pub static RSA_PKCS1_2048_8192_SHA512: &dyn SignatureVerificationAlgorithm =
    &VerificationAlgorithm {
        public_key_alg_id: alg_id::RSA_ENCRYPTION,
        signature_alg_id: alg_id::RSA_PKCS1_SHA512,
        kind: Kind::RsaPkcs1(Hash::Sha512, 2048 / 8),
    };

/// RSA PKCS#1 1.5 signatures using SHA-256 for keys of 2048-8192 bits,
/// with illegally absent AlgorithmIdentifier parameters.
///
/// RFC 4055 says on sha256WithRSAEncryption and company:
///
/// >   When any of these four object identifiers appears within an
/// >   AlgorithmIdentifier, the parameters MUST be NULL.  Implementations
/// >   MUST accept the parameters being absent as well as present.
///
/// This algorithm covers the absent case, [`RSA_PKCS1_2048_8192_SHA256`] covers
/// the present case.
pub static RSA_PKCS1_2048_8192_SHA256_ABSENT_PARAMS: &dyn SignatureVerificationAlgorithm =
    &VerificationAlgorithm {
        public_key_alg_id: alg_id::RSA_ENCRYPTION,
        // sha256WithRSAEncryption (1.2.840.113549.1.1.11), without parameters.
        signature_alg_id: AlgorithmIdentifier::from_slice(&[
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b,
        ]),
        kind: Kind::RsaPkcs1(Hash::Sha256, 2048 / 8),
    };

/// RSA PKCS#1 1.5 signatures using SHA-384 for keys of 2048-8192 bits,
/// with illegally absent AlgorithmIdentifier parameters.
///
/// This algorithm covers the absent case, [`RSA_PKCS1_2048_8192_SHA384`] covers
/// the present case.
pub static RSA_PKCS1_2048_8192_SHA384_ABSENT_PARAMS: &dyn SignatureVerificationAlgorithm =
    &VerificationAlgorithm {
        public_key_alg_id: alg_id::RSA_ENCRYPTION,
        // sha384WithRSAEncryption (1.2.840.113549.1.1.12), without parameters.
        signature_alg_id: AlgorithmIdentifier::from_slice(&[
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0c,
        ]),
        kind: Kind::RsaPkcs1(Hash::Sha384, 2048 / 8),
    };

/// RSA PKCS#1 1.5 signatures using SHA-512 for keys of 2048-8192 bits,
/// with illegally absent AlgorithmIdentifier parameters.
///
/// This algorithm covers the absent case, [`RSA_PKCS1_2048_8192_SHA512`] covers
/// the present case.
pub static RSA_PKCS1_2048_8192_SHA512_ABSENT_PARAMS: &dyn SignatureVerificationAlgorithm =
    &VerificationAlgorithm {
        public_key_alg_id: alg_id::RSA_ENCRYPTION,
        // sha512WithRSAEncryption (1.2.840.113549.1.1.13), without parameters.
        signature_alg_id: AlgorithmIdentifier::from_slice(&[
            0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0d,
        ]),
        kind: Kind::RsaPkcs1(Hash::Sha512, 2048 / 8),
    };

/// RSA PKCS#1 1.5 signatures using SHA-384 for keys of 3072-8192 bits.
pub static RSA_PKCS1_3072_8192_SHA384: &dyn SignatureVerificationAlgorithm =
    &VerificationAlgorithm {
        public_key_alg_id: alg_id::RSA_ENCRYPTION,
        signature_alg_id: alg_id::RSA_PKCS1_SHA384,
        kind: Kind::RsaPkcs1(Hash::Sha384, 3072 / 8),
    };

/// RSA PSS signatures using SHA-256 for keys of 2048-8192 bits and of
/// type rsaEncryption; see [RFC 4055 Section 1.2].
///
/// [RFC 4055 Section 1.2]: https://tools.ietf.org/html/rfc4055#section-1.2
pub static RSA_PSS_2048_8192_SHA256_LEGACY_KEY: &dyn SignatureVerificationAlgorithm =
    &VerificationAlgorithm {
        public_key_alg_id: alg_id::RSA_ENCRYPTION,
        signature_alg_id: alg_id::RSA_PSS_SHA256,
        kind: Kind::RsaPss(Hash::Sha256),
    };

/// RSA PSS signatures using SHA-384 for keys of 2048-8192 bits and of
/// type rsaEncryption; see [RFC 4055 Section 1.2].
///
/// [RFC 4055 Section 1.2]: https://tools.ietf.org/html/rfc4055#section-1.2
pub static RSA_PSS_2048_8192_SHA384_LEGACY_KEY: &dyn SignatureVerificationAlgorithm =
    &VerificationAlgorithm {
        public_key_alg_id: alg_id::RSA_ENCRYPTION,
        signature_alg_id: alg_id::RSA_PSS_SHA384,
        kind: Kind::RsaPss(Hash::Sha384),
    };

/// RSA PSS signatures using SHA-512 for keys of 2048-8192 bits and of
/// type rsaEncryption; see [RFC 4055 Section 1.2].
///
/// [RFC 4055 Section 1.2]: https://tools.ietf.org/html/rfc4055#section-1.2
pub static RSA_PSS_2048_8192_SHA512_LEGACY_KEY: &dyn SignatureVerificationAlgorithm =
    &VerificationAlgorithm {
        public_key_alg_id: alg_id::RSA_ENCRYPTION,
        signature_alg_id: alg_id::RSA_PSS_SHA512,
        kind: Kind::RsaPss(Hash::Sha512),
    };

/// ED25519 signatures according to RFC 8410
pub static ED25519: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ED25519,
    signature_alg_id: alg_id::ED25519,
    kind: Kind::Ed25519,
};

/// ML-DSA signatures using the [4, 4] matrix (security strength category 2).
pub static ML_DSA_44: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ML_DSA_44,
    signature_alg_id: alg_id::ML_DSA_44,
    kind: Kind::MlDsa44,
};

/// ML-DSA signatures using the [6, 5] matrix (security strength category 3).
pub static ML_DSA_65: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ML_DSA_65,
    signature_alg_id: alg_id::ML_DSA_65,
    kind: Kind::MlDsa65,
};

/// ML-DSA signatures using the [8, 7] matrix (security strength category 5).
pub static ML_DSA_87: &dyn SignatureVerificationAlgorithm = &VerificationAlgorithm {
    public_key_alg_id: alg_id::ML_DSA_87,
    signature_alg_id: alg_id::ML_DSA_87,
    kind: Kind::MlDsa87,
};
