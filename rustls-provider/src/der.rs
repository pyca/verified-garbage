//! The DER structures of keys and signatures, read and written with
//! rust-asn1.

// rust-asn1's `ParseError` is large, in the code its derives generate.
#![allow(clippy::result_large_err)]

use alloc::vec::Vec;

/// `AlgorithmIdentifier` (RFC 5280 §4.1.1.2).
#[derive(asn1::Asn1Read)]
pub(crate) struct AlgorithmIdentifier<'a> {
    pub(crate) oid: asn1::ObjectIdentifier,
    pub(crate) params: Option<asn1::Tlv<'a>>,
}

/// `OneAsymmetricKey` (RFC 5958 §2), which includes PKCS #8's
/// `PrivateKeyInfo` (version 0).
#[derive(asn1::Asn1Read)]
pub(crate) struct OneAsymmetricKey<'a> {
    pub(crate) version: u8,
    pub(crate) algorithm: AlgorithmIdentifier<'a>,
    pub(crate) private_key: &'a [u8],
    #[implicit(0)]
    pub(crate) _attributes: Option<asn1::SetOf<'a, asn1::Tlv<'a>>>,
    #[implicit(1)]
    pub(crate) public_key: Option<asn1::BitString<'a>>,
}

/// `RSAPrivateKey` (RFC 8017 §A.1.2), two-prime (version 0) only.
#[derive(asn1::Asn1Read)]
pub(crate) struct RsaPrivateKey<'a> {
    pub(crate) version: u8,
    pub(crate) n: asn1::BigUint<'a>,
    pub(crate) e: asn1::BigUint<'a>,
    pub(crate) d: asn1::BigUint<'a>,
    pub(crate) p: asn1::BigUint<'a>,
    pub(crate) q: asn1::BigUint<'a>,
    pub(crate) dp: asn1::BigUint<'a>,
    pub(crate) dq: asn1::BigUint<'a>,
    pub(crate) qinv: asn1::BigUint<'a>,
}

/// `RSAPublicKey` (RFC 8017 §A.1.1).
#[derive(asn1::Asn1Read, asn1::Asn1Write)]
pub(crate) struct RsaPublicKey<'a> {
    pub(crate) n: asn1::BigUint<'a>,
    pub(crate) e: asn1::BigUint<'a>,
}

/// `ECPrivateKey` (RFC 5915 §3).
#[derive(asn1::Asn1Read)]
pub(crate) struct EcPrivateKey<'a> {
    pub(crate) version: u8,
    pub(crate) private_key: &'a [u8],
    #[explicit(0)]
    pub(crate) parameters: Option<asn1::ObjectIdentifier>,
    #[explicit(1)]
    pub(crate) public_key: Option<asn1::BitString<'a>>,
}

/// `Ecdsa-Sig-Value` (RFC 3279 §2.2.3).
#[derive(asn1::Asn1Read, asn1::Asn1Write)]
pub(crate) struct EcdsaSigValue<'a> {
    pub(crate) r: asn1::BigUint<'a>,
    pub(crate) s: asn1::BigUint<'a>,
}

/// An ML-DSA private key (draft-ietf-lamps-dilithium-certificates §6):
/// `seed [0] IMPLICIT OCTET STRING`, `expandedKey OCTET STRING`, or `both`.
#[derive(asn1::Asn1Read)]
pub(crate) enum MlDsaPrivateKey<'a> {
    #[implicit(0)]
    Seed(&'a [u8]),
    ExpandedKey(#[allow(dead_code)] &'a [u8]),
    Both(MlDsaBoth<'a>),
}

#[derive(asn1::Asn1Read)]
pub(crate) struct MlDsaBoth<'a> {
    pub(crate) seed: &'a [u8],
    pub(crate) _expanded_key: &'a [u8],
}

pub(crate) const RSA_ENCRYPTION: asn1::ObjectIdentifier = asn1::oid!(1, 2, 840, 113549, 1, 1, 1);
pub(crate) const EC_PUBLIC_KEY: asn1::ObjectIdentifier = asn1::oid!(1, 2, 840, 10045, 2, 1);
pub(crate) const SECP256R1: asn1::ObjectIdentifier = asn1::oid!(1, 2, 840, 10045, 3, 1, 7);
pub(crate) const SECP384R1: asn1::ObjectIdentifier = asn1::oid!(1, 3, 132, 0, 34);
pub(crate) const SECP521R1: asn1::ObjectIdentifier = asn1::oid!(1, 3, 132, 0, 35);
pub(crate) const ED25519: asn1::ObjectIdentifier = asn1::oid!(1, 3, 101, 112);
pub(crate) const ML_DSA_44: asn1::ObjectIdentifier = asn1::oid!(2, 16, 840, 1, 101, 3, 4, 3, 17);
pub(crate) const ML_DSA_65: asn1::ObjectIdentifier = asn1::oid!(2, 16, 840, 1, 101, 3, 4, 3, 18);
pub(crate) const ML_DSA_87: asn1::ObjectIdentifier = asn1::oid!(2, 16, 840, 1, 101, 3, 4, 3, 19);

/// The bit string `b` as bytes, if it has no unused bits.
pub(crate) fn bit_string_bytes<'a>(b: &asn1::BitString<'a>) -> Option<&'a [u8]> {
    (b.padding_bits() == 0).then(|| b.as_bytes())
}

/// The value of a DER INTEGER's contents without its leading zero bytes.
pub(crate) fn trim(x: &[u8]) -> &[u8] {
    let z = x.iter().take_while(|&&b| b == 0).count();
    &x[z..]
}

/// `x`, at most `N` bytes long without its leading zeros, as `N` bytes,
/// most significant first.
pub(crate) fn left_pad<const N: usize>(x: &[u8]) -> Option<[u8; N]> {
    let x = trim(x);
    let mut out = [0u8; N];
    out.get_mut(N.checked_sub(x.len())?..)?.copy_from_slice(x);
    Some(out)
}

/// `x` as the contents of a DER INTEGER: minimal, with a leading zero if
/// its most significant bit is set.
pub(crate) fn der_uint(x: &[u8]) -> Vec<u8> {
    let x = trim(x);
    let mut out = Vec::with_capacity(x.len() + 1);
    if x.first().is_none_or(|&b| b & 0x80 != 0) {
        out.push(0);
    }
    out.extend_from_slice(x);
    out
}

/// The DER `Ecdsa-Sig-Value` of the fixed-width signature `r ‖ s`.
pub(crate) fn ecdsa_sig_to_der(rs: &[u8]) -> Vec<u8> {
    let (r, s) = rs.split_at(rs.len() / 2);
    let (r, s) = (der_uint(r), der_uint(s));
    asn1::write_single(&EcdsaSigValue {
        r: asn1::BigUint::new(&r).unwrap(),
        s: asn1::BigUint::new(&s).unwrap(),
    })
    .unwrap()
}

/// The fixed-width signature `r ‖ s` of a DER `Ecdsa-Sig-Value`, each
/// `N` bytes.
pub(crate) fn ecdsa_sig_from_der<const N: usize>(der: &[u8]) -> Option<([u8; N], [u8; N])> {
    let sig = asn1::parse_single::<EcdsaSigValue<'_>>(der).ok()?;
    Some((left_pad(sig.r.as_bytes())?, left_pad(sig.s.as_bytes())?))
}
