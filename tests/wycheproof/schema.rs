//! The groups' and tests' fields that several Wycheproof test files read
//! the same way, defined once.
//!
//! Each file had its own copy, so the harness's generic code
//! (`TestFile<P, T>`, its groups and tests, `par_tests`) and each copy's
//! reader were compiled again for every file. Each type is built on the
//! architectures of the tests that use it.

use super::harness::Hex;
use crate::json_struct;

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
json_struct! {
    /// A message and its signature (the `*Verify` schemas).
    pub struct SigCase {
        pub msg: Hex,
        pub sig: Hex,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
json_struct! {
    /// An elliptic curve public key: the curve's name and the point,
    /// uncompressed.
    pub struct EcPublicKey {
        pub curve: String,
        pub uncompressed: Hex,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
json_struct! {
    /// An ECDSA group: the public key and the hash function's name.
    pub struct EcdsaGroup {
        #[json(rename = "publicKey")]
        pub public_key: EcPublicKey,
        pub sha: String,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
json_struct! {
    /// A key agreement: the peer's public key, the private key and the
    /// shared secret.
    pub struct EcdhCase {
        pub public: Hex,
        pub private: Hex,
        pub shared: Hex,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
json_struct! {
    /// A group of one curve, by name.
    pub struct CurveGroup {
        pub curve: String,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]
json_struct! {
    /// A group of one curve and one encoding of the public keys.
    pub struct CurveEncodingGroup {
        pub curve: String,
        pub encoding: String,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
json_struct! {
    /// An authenticated encryption: key, IV, associated data, message,
    /// ciphertext and tag.
    pub struct AeadCase {
        pub key: Hex,
        pub iv: Hex,
        pub aad: Hex,
        pub msg: Hex,
        pub ct: Hex,
        pub tag: Hex,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
json_struct! {
    /// A group of a cipher's or MAC's sizes, in bits: of the key, the IV
    /// and the tag, those that the schema has.
    pub struct SizesGroup {
        #[json(rename = "keySize")]
        pub key_size: Option<usize>,
        #[json(rename = "ivSize")]
        pub iv_size: Option<usize>,
        #[json(rename = "tagSize")]
        pub tag_size: Option<usize>,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
json_struct! {
    /// A MAC: key, message and tag.
    pub struct MacCase {
        pub key: Hex,
        pub msg: Hex,
        pub tag: Hex,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
json_struct! {
    /// An unauthenticated encryption: key, IV, message and ciphertext.
    pub struct CipherCase {
        pub key: Hex,
        pub iv: Hex,
        pub msg: Hex,
        pub ct: Hex,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
json_struct! {
    /// An EdDSA public key: the curve's name and the key.
    pub struct EdPublicKey {
        pub curve: String,
        pub pk: Hex,
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
json_struct! {
    /// An EdDSA group: its public key.
    pub struct EdGroup {
        #[json(rename = "publicKey")]
        pub public_key: EdPublicKey,
    }
}

#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
json_struct! {
    /// An RSA private key, with its CRT values.
    pub struct RsaPrivateKey {
        pub modulus: Hex,
        #[json(rename = "privateExponent")]
        pub private_exponent: Hex,
        #[json(rename = "publicExponent")]
        pub public_exponent: Hex,
        pub prime1: Hex,
        pub prime2: Hex,
        pub exponent1: Hex,
        pub exponent2: Hex,
        pub coefficient: Hex,
    }
}

#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
json_struct! {
    /// A group of one RSA private key.
    pub struct RsaPrivateKeyGroup {
        #[json(rename = "privateKey")]
        pub private_key: RsaPrivateKey,
    }
}

#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
json_struct! {
    /// An RSA public key.
    pub struct RsaPublicKey {
        pub modulus: Hex,
        #[json(rename = "publicExponent")]
        pub public_exponent: Hex,
    }
}

#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
json_struct! {
    /// A group of one RSA public key and one hash function, by name.
    pub struct RsaPublicKeyGroup {
        #[json(rename = "publicKey")]
        pub public_key: RsaPublicKey,
        pub sha: String,
    }
}

#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
json_struct! {
    /// A message.
    pub struct MsgCase {
        pub msg: Hex,
    }
}

#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
json_struct! {
    /// A message and its encryption.
    pub struct EncryptCase {
        pub msg: Hex,
        pub ct: Hex,
    }
}

#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
json_struct! {
    /// An RSA private key as any RSA test file gives it, which may leave
    /// out any field but the public exponent: for the tests of every file's
    /// two-prime keys.
    pub struct RsaAnyPrivateKey {
        #[json(rename = "publicExponent")]
        pub public_exponent: Hex,
        pub modulus: Option<Hex>,
        #[json(rename = "privateExponent")]
        pub private_exponent: Option<Hex>,
        pub prime1: Option<Hex>,
        pub prime2: Option<Hex>,
        pub exponent1: Option<Hex>,
        pub exponent2: Option<Hex>,
        pub coefficient: Option<Hex>,
        #[json(rename = "otherPrimeInfos")]
        pub other_prime_infos: Option<serde_json::Value>,
    }
}

#[cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]
json_struct! {
    /// A group of any RSA test file, which may have a private key.
    pub struct RsaAnyKeyGroup {
        #[json(rename = "privateKey")]
        pub private_key: Option<RsaAnyPrivateKey>,
    }
}
