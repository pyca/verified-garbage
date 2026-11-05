//! Deterministic ECDSA known-answer tests from the vendored RFC 6979:
//! §A.2.3 (P-192), §A.2.4 (P-224), §A.2.5 (P-256), §A.2.6 (P-384) and §A.2.7 (P-521), each the private
//! key, its public key, and its signatures of "sample" and "test" with the
//! hash functions the curve signs with: on x86-64 and PPC64LE every hash function the
//! RFC signs with (SHA-1 and the SHA-2 family).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

mod p192;
mod p224;
mod p256;
mod p384;
mod p521;

use verified_garbage_test_vectors::unhex;

/// The errors' messages.

#[test]
fn errors() {
    use verified_garbage::ecdsa::Error;
    assert_eq!(Error::InvalidKey.to_string(), "invalid ECDSA private key");
    assert_eq!(
        Error::InvalidSignature.to_string(),
        "invalid ECDSA signature"
    );
}

/// The hex value of the first line from `lines[*i..]` that begins with
/// `label`, continued on the lines after it that are only hex digits, in
/// `N` bytes (P-521's values have an odd number of digits); `*i` moves past
/// it.
fn value<const N: usize>(lines: &[&str], i: &mut usize, label: &str) -> [u8; N] {
    while !lines[*i].starts_with(label) {
        *i += 1;
    }
    let mut hex = lines[*i][label.len()..].to_string();
    *i += 1;
    while !lines[*i].is_empty() && lines[*i].bytes().all(|b| b.is_ascii_hexdigit()) {
        hex.push_str(lines[*i]);
        *i += 1;
    }
    unhex(&format!("{hex:0>width$}", width = 2 * N))
        .try_into()
        .unwrap()
}

/// A value continued over several lines, read on every architecture (only
/// parsed, not signed with): P-521's order, `q` of §A.2.7, which is `2^521`
/// less a number below `2^260`.
#[test]
fn multiline_value() {
    let rfc = crate::vectors::text("vectors/rfc6979/rfc6979.txt");
    let text = rfc
        .split_once("\nA.2.7.  ECDSA, 521 Bits (Prime Field)\n")
        .unwrap()
        .1;
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let mut i = 0;
    let q: [u8; 66] = value(&lines, &mut i, "q = ");
    assert_eq!(q[0], 1);
    assert!(q[1..=32].iter().all(|&b| b == 0xff));
}

/// Each hash function, message and the `r ‖ s` of its signature.
type Signatures<const S: usize> = Vec<(&'static str, String, [u8; S])>;

/// From the section `title`: `q`, `x`, `U = 04 ‖ Ux ‖ Uy`, and the
/// signatures with the hash functions `hashes`.
fn section<const Q: usize, const U: usize, const S: usize>(
    title: &str,
    hashes: &[&'static str],
) -> ([u8; Q], [u8; Q], [u8; U], Signatures<S>) {
    let rfc = crate::vectors::text("vectors/rfc6979/rfc6979.txt");
    let text = rfc.split_once(title).unwrap().1;
    let text = text.split_once("\nA.").unwrap().0;
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let mut i = 0;
    let q = value(&lines, &mut i, "q = ");
    let x = value(&lines, &mut i, "x = ");
    let mut u = [4; U];
    u[1..=Q].copy_from_slice(&value::<Q>(&lines, &mut i, "Ux = "));
    u[Q + 1..].copy_from_slice(&value::<Q>(&lines, &mut i, "Uy = "));
    let mut signatures = Vec::new();
    while i < lines.len() {
        let line = lines[i];
        i += 1;
        let Some((hash, message)) = hashes.iter().find_map(|hash| {
            line.strip_prefix(&format!("With {hash}, message = \""))
                .map(|m| (*hash, m))
        }) else {
            continue;
        };
        let message = message.strip_suffix("\":").unwrap();
        let mut rs = [0; S];
        rs[..Q].copy_from_slice(&value::<Q>(&lines, &mut i, "r = "));
        rs[Q..].copy_from_slice(&value::<Q>(&lines, &mut i, "s = "));
        signatures.push((hash, message.to_string(), rs));
    }
    assert_eq!(signatures.len(), 2 * hashes.len());
    (q, x, u, signatures)
}

/// The signatures with `H`, named `hash` in RFC 6979, of the section
/// `title`, of the message and of its hash; they verify, of the message and
/// of its hash, and not of another message.
#[cfg(any(
    target_arch = "x86_64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
fn sign_with<C, H, const Q: usize, const U: usize, const S: usize>(title: &str, hash: &'static str)
where
    C: verified_garbage::ecdsa::Curve<
            PrivateKey = [u8; Q],
            PublicKey = [u8; U],
            Signature = [u8; S],
        >,
    H: verified_garbage::ecdsa::SignatureHash<C>,
{
    use verified_garbage::ecdsa::{Error, SigningKey, VerifyingKey};
    let (_, x, u, signatures) = section::<Q, U, S>(title, &[hash]);
    let key = SigningKey::<C>::from_bytes(&x);
    let public = VerifyingKey::<C>::from_bytes(&u);
    for (_, message, rs) in &signatures {
        let m = message.as_bytes();
        let digest = H::digest(m);
        assert_eq!(key.sign::<H>(m), Ok(*rs), "{hash} {message}");
        assert_eq!(
            key.sign_prehashed::<H>(&digest),
            Ok(*rs),
            "{hash} {message}"
        );
        assert_eq!(public.verify::<H>(m, rs), Ok(()), "{hash} {message}");
        assert_eq!(
            public.verify_prehashed::<H>(&digest, rs),
            Ok(()),
            "{hash} {message}"
        );
        assert_eq!(
            public.verify::<H>(b"other", rs),
            Err(Error::InvalidSignature)
        );
    }
}

/// With `H`, which RFC 6979 does not sign with (MD5, SHA-512/224,
/// SHA-512/256), the key of the section `title` signs: the signature of the
/// message is that of its hash, verifies with the public key, and not of
/// another message.
#[cfg(any(
    target_arch = "x86_64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
fn round_trip<C, H, const Q: usize, const U: usize, const S: usize>(title: &str)
where
    C: verified_garbage::ecdsa::Curve<
            PrivateKey = [u8; Q],
            PublicKey = [u8; U],
            Signature = [u8; S],
        >,
    H: verified_garbage::ecdsa::SignatureHash<C>,
{
    use verified_garbage::ecdsa::{Error, SigningKey, VerifyingKey};
    let (_, x, u, _) = section::<Q, U, S>(title, &[]);
    let key = SigningKey::<C>::from_bytes(&x);
    let public = VerifyingKey::<C>::from_bytes(&u);
    for m in [&b"sample"[..], b"test"] {
        let rs = key.sign::<H>(m).unwrap();
        assert_eq!(key.sign_prehashed::<H>(&H::digest(m)), Ok(rs));
        assert_eq!(public.verify::<H>(m, &rs), Ok(()));
        assert_eq!(
            public.verify::<H>(b"other", &rs),
            Err(Error::InvalidSignature)
        );
    }
}

/// The hash functions with HMAC that RFC 6979 does not sign with, on every
/// curve of the RFC.
#[cfg(any(
    target_arch = "x86_64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
#[test]
fn other_hashes() {
    use verified_garbage::ecdsa::{P192, P224, P256, P384, P521};
    use verified_garbage::hashes::md5::Md5;
    use verified_garbage::hashes::sha512_224::Sha512_224;
    use verified_garbage::hashes::sha512_256::Sha512_256;
    const A3: &str = "\nA.2.3.  ECDSA, 192 Bits (Prime Field)\n";
    const A4: &str = "\nA.2.4.  ECDSA, 224 Bits (Prime Field)\n";
    const A5: &str = "\nA.2.5.  ECDSA, 256 Bits (Prime Field)\n";
    const A6: &str = "\nA.2.6.  ECDSA, 384 Bits (Prime Field)\n";
    const A7: &str = "\nA.2.7.  ECDSA, 521 Bits (Prime Field)\n";
    round_trip::<P192, Md5, 24, 49, 48>(A3);
    round_trip::<P192, Sha512_224, 24, 49, 48>(A3);
    round_trip::<P192, Sha512_256, 24, 49, 48>(A3);
    round_trip::<P224, Md5, 28, 57, 56>(A4);
    round_trip::<P224, Sha512_224, 28, 57, 56>(A4);
    round_trip::<P224, Sha512_256, 28, 57, 56>(A4);
    round_trip::<P256, Md5, 32, 65, 64>(A5);
    round_trip::<P256, Sha512_224, 32, 65, 64>(A5);
    round_trip::<P256, Sha512_256, 32, 65, 64>(A5);
    round_trip::<P384, Md5, 48, 97, 96>(A6);
    round_trip::<P384, Sha512_224, 48, 97, 96>(A6);
    round_trip::<P384, Sha512_256, 48, 97, 96>(A6);
    round_trip::<P521, Md5, 66, 133, 132>(A7);
    round_trip::<P521, Sha512_224, 66, 133, 132>(A7);
    round_trip::<P521, Sha512_256, 66, 133, 132>(A7);
}

/// The integer `x + delta` (mod 2^(8N)) of the `N` bytes `x`.
fn add<const N: usize>(x: &[u8; N], delta: i16) -> [u8; N] {
    let mut out = *x;
    let mut carry = delta;
    for b in out.iter_mut().rev() {
        let v = i16::from(*b) + carry;
        *b = v.rem_euclid(256) as u8;
        carry = v.div_euclid(256);
    }
    out
}
