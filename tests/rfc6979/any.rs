//! RFC 6979 §A.2.3–§A.2.7 with every hash function they sign with (SHA-1,
//! SHA-224, SHA-256, SHA-384 and SHA-512) over P-192, P-224, P-256, P-384
//! and P-521, on x86-64, where every curve signs with SHA-1 and each SHA-2
//! function; and, with those the RFC has no signatures with (SHA-512/224
//! and SHA-512/256) and over the curves it has none over (secp256k1 and
//! the brainpool curves), signatures that verify, and only of their
//! message, whichever tier of implementations of the hash functions this
//! CPU runs (the tests' names select them for each CPU configuration CI
//! tests).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

#[cfg(target_arch = "x86_64")]
mod x86_64 {
    use verified_garbage::ecdsa::{
        BrainpoolP256r1, BrainpoolP384r1, BrainpoolP512r1, Curve, Error, P192, P224, P256, P384,
        P521, Secp256k1, SignatureHash, SigningKey, VerifyingKey,
    };
    use verified_garbage::hashes::HashFunction;
    use verified_garbage::hashes::sha1::Sha1;
    use verified_garbage::hashes::sha224::Sha224;
    use verified_garbage::hashes::sha256::Sha256;
    use verified_garbage::hashes::sha384::Sha384;
    use verified_garbage::hashes::sha512::Sha512;
    use verified_garbage::hashes::sha512_224::Sha512_224;
    use verified_garbage::hashes::sha512_256::Sha512_256;

    /// The hash functions of RFC 6979's signatures.
    const HASHES: [&str; 5] = ["SHA-1", "SHA-224", "SHA-256", "SHA-384", "SHA-512"];

    /// A curve over which each of the hash functions signs, by its name.
    trait Signs: Curve<Signature: PartialEq + core::fmt::Debug> + Sized {
        /// The signature of `message` with the hash function named `hash`,
        /// of the message and of its hash, which must agree.
        fn sign(key: &SigningKey<Self>, hash: &str, message: &[u8]) -> Result<Self::Signature, Error>;

        /// Whether `rs` verifies for `message` with the hash function named
        /// `hash`, of the message and of its hash, which must agree.
        fn verify(
            key: &VerifyingKey<Self>,
            hash: &str,
            message: &[u8],
            rs: &Self::Signature,
        ) -> Result<(), Error>;
    }

    fn sign_one<C, H>(key: &SigningKey<C>, message: &[u8]) -> Result<C::Signature, Error>
    where
        C: Curve<Signature: PartialEq + core::fmt::Debug>,
        H: SignatureHash<C>,
    {
        let signed = key.sign::<H>(message);
        assert_eq!(signed, key.sign_prehashed::<H>(&H::digest(message)));
        signed
    }

    fn verify_one<C: Curve, H: SignatureHash<C>>(
        key: &VerifyingKey<C>,
        message: &[u8],
        rs: &C::Signature,
    ) -> Result<(), Error> {
        let verified = key.verify::<H>(message, rs);
        assert_eq!(verified, key.verify_prehashed::<H>(&H::digest(message), rs));
        verified
    }

    impl<C> Signs for C
    where
        C: Curve<Signature: PartialEq + core::fmt::Debug>,
        Sha1: SignatureHash<C>,
        Sha224: SignatureHash<C>,
        Sha256: SignatureHash<C>,
        Sha384: SignatureHash<C>,
        Sha512: SignatureHash<C>,
        Sha512_224: SignatureHash<C>,
        Sha512_256: SignatureHash<C>,
    {
        fn sign(key: &SigningKey<C>, hash: &str, message: &[u8]) -> Result<C::Signature, Error> {
            match hash {
                "SHA-1" => sign_one::<C, Sha1>(key, message),
                "SHA-224" => sign_one::<C, Sha224>(key, message),
                "SHA-256" => sign_one::<C, Sha256>(key, message),
                "SHA-384" => sign_one::<C, Sha384>(key, message),
                "SHA-512" => sign_one::<C, Sha512>(key, message),
                "SHA-512/224" => sign_one::<C, Sha512_224>(key, message),
                "SHA-512/256" => sign_one::<C, Sha512_256>(key, message),
                _ => unreachable!("{hash}"),
            }
        }

        fn verify(
            key: &VerifyingKey<C>,
            hash: &str,
            message: &[u8],
            rs: &C::Signature,
        ) -> Result<(), Error> {
            match hash {
                "SHA-1" => verify_one::<C, Sha1>(key, message, rs),
                "SHA-224" => verify_one::<C, Sha224>(key, message, rs),
                "SHA-256" => verify_one::<C, Sha256>(key, message, rs),
                "SHA-384" => verify_one::<C, Sha384>(key, message, rs),
                "SHA-512" => verify_one::<C, Sha512>(key, message, rs),
                "SHA-512/224" => verify_one::<C, Sha512_224>(key, message, rs),
                "SHA-512/256" => verify_one::<C, Sha512_256>(key, message, rs),
                _ => unreachable!("{hash}"),
            }
        }
    }

    /// The RFC's signatures from the section `title`, with each hash
    /// function: the key signs them, and they verify with the public key.
    fn rfc<C, const Q: usize, const U: usize, const S: usize>(title: &str)
    where
        C: Signs + Curve<PrivateKey = [u8; Q], PublicKey = [u8; U], Signature = [u8; S]>,
    {
        let (_, x, u, signatures) = super::super::section::<Q, U, S>(title, &HASHES);
        let key = SigningKey::<C>::from_bytes(&x);
        let public = VerifyingKey::<C>::from_bytes(&u);
        for (hash, message, rs) in &signatures {
            let message = message.as_bytes();
            assert_eq!(C::sign(&key, hash, message), Ok(*rs), "{hash}");
            assert_eq!(C::verify(&public, hash, message, rs), Ok(()), "{hash}");
        }
    }

    /// With each hash function, a signature by `key` verifies with `public`,
    /// and not of another message or with another hash function.
    fn round_trip<C: Signs>(key: &SigningKey<C>, public: &VerifyingKey<C>, hashes: &[&str]) {
        let bad = Err(Error::InvalidSignature);
        for hash in hashes {
            let rs = C::sign(key, hash, b"sample").unwrap();
            assert_eq!(C::verify(public, hash, b"sample", &rs), Ok(()), "{hash}");
            assert_eq!(C::verify(public, hash, b"test", &rs), bad, "{hash}");
            let other = if *hash == "SHA-256" { "SHA-384" } else { "SHA-256" };
            assert_eq!(C::verify(public, other, b"sample", &rs), bad, "{hash}");
        }
    }

    /// The hash functions the RFC has no signatures with.
    const OTHERS: [&str; 2] = ["SHA-512/224", "SHA-512/256"];

    /// Every hash function.
    const ALL: [&str; 7] = [
        "SHA-1",
        "SHA-224",
        "SHA-256",
        "SHA-384",
        "SHA-512",
        "SHA-512/224",
        "SHA-512/256",
    ];

    /// A private key: `01 11 … 11`, below the order of every curve.
    fn key<const Q: usize>() -> [u8; Q] {
        let mut d = [0x11; Q];
        d[0] = 0x01;
        d
    }

    /// The curve's RFC signatures, with each hash function, and signatures
    /// with the others that verify.
    macro_rules! rfc_curve {
        ($name:ident, $curve:ty, $title:literal, $q:literal, $u:literal, $s:literal) => {
            #[test]
            fn $name() {
                rfc::<$curve, $q, $u, $s>($title);
                let (_, x, u, _) = super::super::section::<$q, $u, $s>($title, &HASHES);
                round_trip(
                    &SigningKey::<$curve>::from_bytes(&x),
                    &VerifyingKey::<$curve>::from_bytes(&u),
                    &OTHERS,
                );
            }
        };
    }

    rfc_curve!(p192, P192, "\nA.2.3.  ECDSA, 192 Bits (Prime Field)\n", 24, 49, 48);
    rfc_curve!(p224, P224, "\nA.2.4.  ECDSA, 224 Bits (Prime Field)\n", 28, 57, 56);
    rfc_curve!(p256, P256, "\nA.2.5.  ECDSA, 256 Bits (Prime Field)\n", 32, 65, 64);
    rfc_curve!(p384, P384, "\nA.2.6.  ECDSA, 384 Bits (Prime Field)\n", 48, 97, 96);
    rfc_curve!(p521, P521, "\nA.2.7.  ECDSA, 521 Bits (Prime Field)\n", 66, 133, 132);

    /// Signatures with each hash function over the curves the RFC has no
    /// signatures over, which verify.
    macro_rules! other_curve {
        ($name:ident, $curve:ty, $q:literal) => {
            #[test]
            fn $name() {
                let key = SigningKey::<$curve>::from_bytes(&key::<$q>());
                let public = VerifyingKey::<$curve>::from_bytes(&key.public_key().unwrap());
                round_trip(&key, &public, &ALL);
            }
        };
    }

    other_curve!(secp256k1, Secp256k1, 32);
    other_curve!(brainpoolp256r1, BrainpoolP256r1, 32);
    other_curve!(brainpoolp384r1, BrainpoolP384r1, 48);
    other_curve!(brainpoolp512r1, BrainpoolP512r1, 64);
}
