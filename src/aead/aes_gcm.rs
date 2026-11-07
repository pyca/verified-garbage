//! AES-GCM (NIST SP 800-38D) with 128-, 192- and 256-bit keys, for whole
//! messages and incrementally.
//!
//! A nonce must never be used twice with the same key. **An
//! [`AesGcmDecryptor`]'s `update` returns plaintext that has not been
//! authenticated**: act on none of it before its `finalize` succeeds, or, when
//! the message fits in memory, use [`AesGcm::decrypt_in_place`], which checks
//! the tag before it decrypts.
//!
//! # Tags
//!
//! Encryption returns the full 16-byte tag; a protocol that sends a shorter one
//! sends its first bytes. Decryption takes a `&[u8; 16]` or, for a truncated
//! tag, a `&[u8; N]` with `N` from 4 to 16 fixed at compile time
//! ([`AesGcm::decrypt_in_place_truncated`],
//! [`AesGcmDecryptor::finalize_truncated`]), never a slice, whose length often
//! comes from the message: splitting the last 16 bytes off a 4-byte message
//! would check a 4-byte tag, forged with probability 2⁻³² rather than 2⁻¹²⁸. SP
//! 800-38D §5.2.1.2 allows only 4, 8 and 12 to 16 bytes (5–7 and 9–11 are
//! extensions), and 4 and 8 only within its Appendix C's limits on message
//! lengths and decryptions per key, which the caller enforces.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::gcm::{
    vg_aes_gcm_init_auto, vg_aes_gcm_open_auto, vg_aes_gcm_open_to_auto, vg_aes_gcm_seal_auto,
    vg_aes_gcm_seal_gather_auto, vg_aes_gcm_stream_aad_auto, vg_aes_gcm_stream_decrypt_auto,
    vg_aes_gcm_stream_encrypt_auto, vg_aes_gcm_stream_finish_auto, vg_aes_gcm_stream_init_auto,
    vg_aes_gcm_stream_verify_auto,
};
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
use crate::arch::gcm::{
    VG_AES_GCM_OPEN_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
    VG_AES_GCM_OPEN_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
    VG_AES_GCM_OPEN_PREPARED16_VAES_VPCLMUL_FEATURES,
    VG_AES_GCM_OPEN_TO_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
    VG_AES_GCM_OPEN_TO_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
    VG_AES_GCM_OPEN_TO_PREPARED16_VAES_VPCLMUL_FEATURES,
    VG_AES_GCM_PREPARE_VPCLMUL_AVX512_FEATURES, VG_AES_GCM_PREPARE16_PCLMUL_AVX_CTX_WRITTEN,
    VG_AES_GCM_PREPARE16_PCLMUL_AVX_FEATURES, VG_AES_GCM_PREPARE16_VPCLMUL_CTX_WRITTEN,
    VG_AES_GCM_PREPARE16_VPCLMUL_FEATURES,
    VG_AES_GCM_SEAL_GATHER_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
    VG_AES_GCM_SEAL_GATHER_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
    VG_AES_GCM_SEAL_GATHER_PREPARED16_VAES_VPCLMUL_FEATURES,
    VG_AES_GCM_SEAL_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
    VG_AES_GCM_SEAL_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
    VG_AES_GCM_SEAL_PREPARED16_VAES_VPCLMUL_FEATURES,
    VG_AES_GCM_STREAM_DECRYPT_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
    VG_AES_GCM_STREAM_DECRYPT_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
    VG_AES_GCM_STREAM_DECRYPT_PREPARED16_VAES_VPCLMUL_FEATURES,
    VG_AES_GCM_STREAM_ENCRYPT_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
    VG_AES_GCM_STREAM_ENCRYPT_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
    VG_AES_GCM_STREAM_ENCRYPT_PREPARED16_VAES_VPCLMUL_FEATURES,
    vg_aes_gcm_open_prepared_vaes_vpclmul_avx512, vg_aes_gcm_open_prepared16_aesni_pclmul_avx,
    vg_aes_gcm_open_prepared16_vaes_vpclmul, vg_aes_gcm_open_to_prepared_vaes_vpclmul_avx512,
    vg_aes_gcm_open_to_prepared16_aesni_pclmul_avx, vg_aes_gcm_open_to_prepared16_vaes_vpclmul,
    vg_aes_gcm_prepare_vpclmul_avx512, vg_aes_gcm_prepare16_pclmul_avx,
    vg_aes_gcm_prepare16_vpclmul, vg_aes_gcm_seal_gather_prepared_vaes_vpclmul_avx512,
    vg_aes_gcm_seal_gather_prepared16_aesni_pclmul_avx,
    vg_aes_gcm_seal_gather_prepared16_vaes_vpclmul, vg_aes_gcm_seal_prepared_vaes_vpclmul_avx512,
    vg_aes_gcm_seal_prepared16_aesni_pclmul_avx, vg_aes_gcm_seal_prepared16_vaes_vpclmul,
    vg_aes_gcm_stream_decrypt_prepared_vaes_vpclmul_avx512,
    vg_aes_gcm_stream_decrypt_prepared16_aesni_pclmul_avx,
    vg_aes_gcm_stream_decrypt_prepared16_vaes_vpclmul,
    vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512,
    vg_aes_gcm_stream_encrypt_prepared16_aesni_pclmul_avx,
    vg_aes_gcm_stream_encrypt_prepared16_vaes_vpclmul,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::gcm::{
    VG_AES_GCM_OPEN_WITH_POWERS_AES_FEATURES, VG_AES_GCM_OPEN_WITH_POWERS_AES_SHA3_FEATURES,
    VG_AES_GCM_SEAL_AES_FEATURES, VG_AES_GCM_SEAL_WITH_POWERS_AES_FEATURES,
    VG_AES_GCM_SEAL_WITH_POWERS_AES_SHA3_FEATURES, VG_AES_GCM_STORE_POWERS_AES_FEATURES,
    vg_aes_gcm_open_with_powers_aes, vg_aes_gcm_open_with_powers_aes_sha3,
    vg_aes_gcm_seal_with_powers_aes, vg_aes_gcm_seal_with_powers_aes_sha3,
    vg_aes_gcm_store_powers_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_AESNI_FEATURES, VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES,
    VG_AES_GCM_SEAL_PCLMUL_FEATURES,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_AESNI_PCLMUL_AVX_FEATURES, VG_AES_GCM_SEAL_AESNI_VPCLMUL_FEATURES,
    VG_AES_GCM_SEAL_VAES_FEATURES, VG_AES_GCM_SEAL_VAES_PCLMUL_FEATURES,
    VG_AES_GCM_SEAL_VAES_VPCLMUL_AVX512_FEATURES, VG_AES_GCM_SEAL_VAES_VPCLMUL_FEATURES,
    VG_AES_GCM_SEAL_VPCLMUL_FEATURES,
};
#[cfg(any(
    all(target_arch = "x86_64", feature = "alloc"),
    target_arch = "aarch64"
))]
use crate::cpu::detected;
use crate::error::InvalidKeyLength;
use crate::zeroize::{zeroize, zeroize_raw};
use core::mem::MaybeUninit;
use verified_garbage_cpu::Features;

/// A 16-byte block.
type Block = [u8; 16];

/// What a key keeps of its key context: on x86-64, the key context with the
/// powers of the hash subkey (`Ctx`), whose first 256 bytes are the key
/// context of `vg_aes_gcm_init` (`AesGcm::key`) and whose powers
/// `AesGcm::new` computes if the backend has `_prepared` instances;
/// elsewhere, the key context of `vg_aes_gcm_init` alone.
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
type KeyCtx = Ctx;
#[cfg(not(all(target_arch = "x86_64", feature = "alloc")))]
type KeyCtx = [u64; 32];

/// The largest plaintext (and ciphertext), in bytes: `2^39 − 256` bits
/// (SP 800-38D §5.2.1.1).
const MAX_TEXT: u64 = (1 << 36) - 32;

/// The largest additional data, in bytes: `2^64 − 1` bits, rounded down to
/// whole bytes (SP 800-38D §5.2.1.1).
const MAX_AAD: u64 = (1 << 61) - 1;

/// The implementations of AES-GCM, by suffix, which `aes_gcm_siv` chooses
/// its own instances by (`AesGcm` calls the dispatchers of
/// `crate::arch::dispatch::gcm`). (A product of `crate::cipher::aes::Backend`
/// and a GHASH backend would let a caller pair them any way; one enum of the
/// variants keeps every `match` exhaustive over exactly the functions that
/// exist.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The baseline implementation.
    Scalar,
    /// `_aesni`.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    AesNi,
    /// `_pclmul`.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    Pclmul,
    /// `_aesni_pclmul`.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    AesNiPclmul,
    /// `_vaes`.
    #[cfg(target_arch = "x86_64")]
    Vaes,
    /// `_vpclmul`.
    #[cfg(target_arch = "x86_64")]
    Vpclmul,
    /// `_vaes_pclmul`.
    #[cfg(target_arch = "x86_64")]
    VaesPclmul,
    /// `_aesni_vpclmul`.
    #[cfg(target_arch = "x86_64")]
    AesNiVpclmul,
    /// `_vaes_vpclmul`.
    #[cfg(target_arch = "x86_64")]
    VaesVpclmul,
    /// `_vaes_vpclmul_avx512`.
    #[cfg(target_arch = "x86_64")]
    VaesVpclmulAvx512,
    /// `_aesni_pclmul_avx`.
    #[cfg(target_arch = "x86_64")]
    AesNiPclmulAvx,
    /// `_aes`.
    #[cfg(target_arch = "aarch64")]
    Aes,
    /// `_aes_sha3`.
    #[cfg(target_arch = "aarch64")]
    AesSha3,
}

/// The variant of a function for `backend`: the baseline one, then those
/// for x86-64 and x86, those for x86-64 alone and those for AArch64, by
/// suffix.
macro_rules! instance {
    ($backend:expr, $scalar:ident,
     x86_64: [$aesni:ident, $pclmul:ident, $aesni_pclmul:ident],
     vaes: [$vaes:ident, $vpclmul:ident, $vaes_pclmul:ident, $aesni_vpclmul:ident,
        $vaes_vpclmul:ident, $vaes_vpclmul_avx512:ident],
     avx: [$aesni_pclmul_avx:ident],
     aarch64: [$aes:ident, $aes_sha3:ident]) => {
        match $backend {
            Backend::Scalar => $scalar,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNi => $aesni,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::Pclmul => $pclmul,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNiPclmul => $aesni_pclmul,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => $vaes,
            #[cfg(target_arch = "x86_64")]
            Backend::Vpclmul => $vpclmul,
            #[cfg(target_arch = "x86_64")]
            Backend::VaesPclmul => $vaes_pclmul,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNiVpclmul => $aesni_vpclmul,
            #[cfg(target_arch = "x86_64")]
            Backend::VaesVpclmul => $vaes_vpclmul,
            #[cfg(target_arch = "x86_64")]
            Backend::VaesVpclmulAvx512 => $vaes_vpclmul_avx512,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNiPclmulAvx => $aesni_pclmul_avx,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => $aes,
            #[cfg(target_arch = "aarch64")]
            Backend::AesSha3 => $aes_sha3,
        }
    };
}
// `aes_gcm_siv` chooses its instances with it too, on its architectures.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub(crate) use instance;

/// The features of the baseline ISA: none.
const BASELINE: Features = Features(0);

impl Backend {
    /// Every implementation, best first, with the features it needs
    /// (computed at compile time, so that choosing one compares bit sets).
    pub(crate) const ALL: &[(Backend, Features)] = &[
        #[cfg(target_arch = "x86_64")]
        (
            Backend::VaesVpclmulAvx512,
            Backend::VaesVpclmulAvx512.features(),
        ),
        #[cfg(target_arch = "x86_64")]
        (Backend::VaesVpclmul, Backend::VaesVpclmul.features()),
        #[cfg(target_arch = "x86_64")]
        (Backend::VaesPclmul, Backend::VaesPclmul.features()),
        #[cfg(target_arch = "x86_64")]
        (Backend::AesNiVpclmul, Backend::AesNiVpclmul.features()),
        #[cfg(target_arch = "x86_64")]
        (Backend::AesNiPclmulAvx, Backend::AesNiPclmulAvx.features()),
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        (Backend::AesNiPclmul, Backend::AesNiPclmul.features()),
        #[cfg(target_arch = "x86_64")]
        (Backend::Vaes, Backend::Vaes.features()),
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        (Backend::AesNi, Backend::AesNi.features()),
        #[cfg(target_arch = "x86_64")]
        (Backend::Vpclmul, Backend::Vpclmul.features()),
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        (Backend::Pclmul, Backend::Pclmul.features()),
        #[cfg(target_arch = "aarch64")]
        (Backend::AesSha3, Backend::AesSha3.features()),
        #[cfg(target_arch = "aarch64")]
        (Backend::Aes, Backend::Aes.features()),
        (Backend::Scalar, Backend::Scalar.features()),
    ];

    /// The CPU features its instances need: `seal`'s; for `AesSha3`, whose
    /// `seal` is `Aes`'s, `seal_with_powers`'s. (`aes_gcm_siv` checks its
    /// own instances' against them: `features_cover_instances`.)
    const fn features(self) -> Features {
        instance!(self, BASELINE,
            x86_64: [VG_AES_GCM_SEAL_AESNI_FEATURES, VG_AES_GCM_SEAL_PCLMUL_FEATURES,
                VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES],
            vaes: [VG_AES_GCM_SEAL_VAES_FEATURES, VG_AES_GCM_SEAL_VPCLMUL_FEATURES,
                VG_AES_GCM_SEAL_VAES_PCLMUL_FEATURES, VG_AES_GCM_SEAL_AESNI_VPCLMUL_FEATURES,
                VG_AES_GCM_SEAL_VAES_VPCLMUL_FEATURES, VG_AES_GCM_SEAL_VAES_VPCLMUL_AVX512_FEATURES],
            avx: [VG_AES_GCM_SEAL_AESNI_PCLMUL_AVX_FEATURES],
            aarch64: [VG_AES_GCM_SEAL_AES_FEATURES, VG_AES_GCM_SEAL_WITH_POWERS_AES_SHA3_FEATURES])
    }
}

/// The best implementation a CPU with the features `f` can run.
pub(crate) fn select(f: Features) -> Backend {
    let best = Backend::ALL.iter().find(|(_, need)| f.contains(*need));
    best.map_or(Backend::Scalar, |(b, _)| *b)
}

/// A family of instances that read the powers of the hash subkey, which a
/// key setup of their own computes: on x86-64, a backend's `_prepared`
/// instances (`VG.Spec.Gcm.PreparedPowersRepr`), or its `_prepared16` ones
/// (`VG.Spec.Gcm.PreparedPowers16Repr`), which read them from the key
/// context `vg_aes_gcm_prepare` makes; on AArch64, its `_with_powers`
/// instances (`VG.Spec.Gcm.Powers8Repr`), which read the powers
/// `vg_aes_gcm_store_powers_aes` stores next to the key context.
///
/// These are the one choice among AES-GCM's implementations not left to
/// the dispatchers (`crate::arch::dispatch::gcm`): a key's powers are laid
/// out for one family, whose functions have contracts of their own, so a
/// key must be set up and then read by the same family, which dispatchers
/// that each choose one function cannot promise. A key uses the family of
/// the implementation the dispatchers choose (`prepared`), where the CPU has
/// the features of all its functions; every other call is a dispatcher's.
#[cfg(any(
    all(target_arch = "x86_64", feature = "alloc"),
    target_arch = "aarch64"
))]
struct Prepared {
    /// The features of all its functions, and of its key setup.
    features: Features,
    seal: SealPrepared,
    open: OpenPrepared,
    #[cfg(target_arch = "x86_64")]
    open_to: OpenToPrepared,
    /// None on AArch64, where `encrypt` copies its pieces and calls `seal`.
    #[cfg(target_arch = "x86_64")]
    seal_gather: SealGatherPrepared,
    #[cfg(target_arch = "x86_64")]
    stream_encrypt: StreamPrepared,
    #[cfg(target_arch = "x86_64")]
    stream_decrypt: StreamPrepared,
    /// `vg_aes_gcm_prepare`, which makes the prepared context from the key
    /// context of `vg_aes_gcm_init`.
    #[cfg(target_arch = "x86_64")]
    prepare: Prepare,
    /// The bytes of the key context it writes (`AesGcm::written`): its
    /// proven `_CTX_WRITTEN`, or all of them.
    #[cfg(target_arch = "x86_64")]
    written: usize,
}

/// `vg_aes_gcm_prepare`.
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
type Prepare = unsafe extern "sysv64" fn(*mut Ctx);

/// The types of the `_prepared` instances on x86-64, on the key context
/// with the powers, `Ctx`.
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
mod prepared_types {
    use super::Ctx;
    pub(super) type SealPrepared = unsafe extern "sysv64" fn(
        *const Ctx,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *mut u8,
        usize,
        *mut [u8; 16],
    );
    pub(super) type OpenPrepared = unsafe extern "sysv64" fn(
        *const Ctx,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *mut u8,
        usize,
        *const u8,
        usize,
    ) -> u32;
    pub(super) type OpenToPrepared = unsafe extern "sysv64" fn(
        *const Ctx,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *mut u8,
        usize,
        *const u8,
        usize,
    ) -> u32;
    pub(super) type SealGatherPrepared = unsafe extern "sysv64" fn(
        *const Ctx,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const [usize; 2],
        usize,
        *mut u8,
        usize,
        *mut [u8; 16],
    );
}
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
use prepared_types::{OpenPrepared, OpenToPrepared, SealGatherPrepared, SealPrepared};
/// The powers of the hash subkey: on x86-64, in a key context of 1024 bytes
/// (`VG.Spec.Gcm.PreparedPowersRepr`), which the `_prepared` instances read
/// alone, and which begins with the key context of `vg_aes_gcm_init`; on
/// AArch64, in 128 bytes (`VG.Spec.Gcm.Powers8Repr`), which the
/// `_with_powers` instances read next to the key context of
/// `vg_aes_gcm_init`.
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
type Ctx = [u64; 128];
#[cfg(target_arch = "aarch64")]
type Ctx = [u64; 16];
/// The `_with_powers` instances of `seal` and `open`: `vg_aes_gcm_seal`'s
/// and `vg_aes_gcm_open`'s arguments, then the powers.
#[cfg(target_arch = "aarch64")]
type SealPrepared = unsafe extern "C" fn(
    *const [u64; 32],
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *mut u8,
    usize,
    *mut [u8; 16],
    *const Ctx,
);
#[cfg(target_arch = "aarch64")]
type OpenPrepared = unsafe extern "C" fn(
    *const [u64; 32],
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *mut u8,
    usize,
    *const u8,
    usize,
    *const Ctx,
) -> u32;

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
type StreamPrepared =
    unsafe extern "sysv64" fn(*const [u64; 128], usize, *mut [u64; 10], u64, u64, *mut u8, usize);

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
static PREPARED_VAES_VPCLMUL_AVX512: Prepared = Prepared {
    features: Features::all(&[
        VG_AES_GCM_PREPARE_VPCLMUL_AVX512_FEATURES,
        VG_AES_GCM_SEAL_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
        VG_AES_GCM_OPEN_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
        VG_AES_GCM_OPEN_TO_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
        VG_AES_GCM_SEAL_GATHER_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
        VG_AES_GCM_STREAM_ENCRYPT_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
        VG_AES_GCM_STREAM_DECRYPT_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
    ]),
    seal: vg_aes_gcm_seal_prepared_vaes_vpclmul_avx512,
    open: vg_aes_gcm_open_prepared_vaes_vpclmul_avx512,
    open_to: vg_aes_gcm_open_to_prepared_vaes_vpclmul_avx512,
    seal_gather: vg_aes_gcm_seal_gather_prepared_vaes_vpclmul_avx512,
    stream_encrypt: vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512,
    stream_decrypt: vg_aes_gcm_stream_decrypt_prepared_vaes_vpclmul_avx512,
    prepare: vg_aes_gcm_prepare_vpclmul_avx512,
    written: size_of::<Ctx>(),
};

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
static PREPARED_VAES_VPCLMUL: Prepared = Prepared {
    features: Features::all(&[
        VG_AES_GCM_PREPARE16_VPCLMUL_FEATURES,
        VG_AES_GCM_SEAL_PREPARED16_VAES_VPCLMUL_FEATURES,
        VG_AES_GCM_OPEN_PREPARED16_VAES_VPCLMUL_FEATURES,
        VG_AES_GCM_OPEN_TO_PREPARED16_VAES_VPCLMUL_FEATURES,
        VG_AES_GCM_SEAL_GATHER_PREPARED16_VAES_VPCLMUL_FEATURES,
        VG_AES_GCM_STREAM_ENCRYPT_PREPARED16_VAES_VPCLMUL_FEATURES,
        VG_AES_GCM_STREAM_DECRYPT_PREPARED16_VAES_VPCLMUL_FEATURES,
    ]),
    seal: vg_aes_gcm_seal_prepared16_vaes_vpclmul,
    open: vg_aes_gcm_open_prepared16_vaes_vpclmul,
    open_to: vg_aes_gcm_open_to_prepared16_vaes_vpclmul,
    seal_gather: vg_aes_gcm_seal_gather_prepared16_vaes_vpclmul,
    stream_encrypt: vg_aes_gcm_stream_encrypt_prepared16_vaes_vpclmul,
    stream_decrypt: vg_aes_gcm_stream_decrypt_prepared16_vaes_vpclmul,
    prepare: vg_aes_gcm_prepare16_vpclmul,
    written: VG_AES_GCM_PREPARE16_VPCLMUL_CTX_WRITTEN,
};

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
static PREPARED_AESNI_PCLMUL_AVX: Prepared = Prepared {
    features: Features::all(&[
        VG_AES_GCM_PREPARE16_PCLMUL_AVX_FEATURES,
        VG_AES_GCM_SEAL_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
        VG_AES_GCM_OPEN_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
        VG_AES_GCM_OPEN_TO_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
        VG_AES_GCM_SEAL_GATHER_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
        VG_AES_GCM_STREAM_ENCRYPT_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
        VG_AES_GCM_STREAM_DECRYPT_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
    ]),
    seal: vg_aes_gcm_seal_prepared16_aesni_pclmul_avx,
    open: vg_aes_gcm_open_prepared16_aesni_pclmul_avx,
    open_to: vg_aes_gcm_open_to_prepared16_aesni_pclmul_avx,
    seal_gather: vg_aes_gcm_seal_gather_prepared16_aesni_pclmul_avx,
    stream_encrypt: vg_aes_gcm_stream_encrypt_prepared16_aesni_pclmul_avx,
    stream_decrypt: vg_aes_gcm_stream_decrypt_prepared16_aesni_pclmul_avx,
    prepare: vg_aes_gcm_prepare16_pclmul_avx,
    written: VG_AES_GCM_PREPARE16_PCLMUL_AVX_CTX_WRITTEN,
};

#[cfg(target_arch = "aarch64")]
static PREPARED_AES: Prepared = Prepared {
    features: Features::all(&[
        VG_AES_GCM_STORE_POWERS_AES_FEATURES,
        VG_AES_GCM_SEAL_WITH_POWERS_AES_FEATURES,
        VG_AES_GCM_OPEN_WITH_POWERS_AES_FEATURES,
    ]),
    seal: vg_aes_gcm_seal_with_powers_aes,
    open: vg_aes_gcm_open_with_powers_aes,
};

#[cfg(target_arch = "aarch64")]
static PREPARED_AES_SHA3: Prepared = Prepared {
    features: Features::all(&[
        VG_AES_GCM_STORE_POWERS_AES_FEATURES,
        VG_AES_GCM_SEAL_WITH_POWERS_AES_SHA3_FEATURES,
        VG_AES_GCM_OPEN_WITH_POWERS_AES_SHA3_FEATURES,
    ]),
    seal: vg_aes_gcm_seal_with_powers_aes_sha3,
    open: vg_aes_gcm_open_with_powers_aes_sha3,
};

/// The implementations of `vg_aes_gcm_seal` that `vg_aes_gcm_seal_auto`
/// ranks first (`VG.Dispatch.gcmX86_64`; on AArch64, `_aes_sha3` before
/// `_aes`), each with its features and its family of instances with powers,
/// if it has one: down to the last with one, which is all `prepared` needs.
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
static RANKED: [(Features, Option<&Prepared>); 5] = [
    (
        VG_AES_GCM_SEAL_VAES_VPCLMUL_AVX512_FEATURES,
        Some(&PREPARED_VAES_VPCLMUL_AVX512),
    ),
    (
        VG_AES_GCM_SEAL_VAES_VPCLMUL_FEATURES,
        Some(&PREPARED_VAES_VPCLMUL),
    ),
    (VG_AES_GCM_SEAL_VAES_PCLMUL_FEATURES, None),
    (VG_AES_GCM_SEAL_AESNI_VPCLMUL_FEATURES, None),
    (
        VG_AES_GCM_SEAL_AESNI_PCLMUL_AVX_FEATURES,
        Some(&PREPARED_AESNI_PCLMUL_AVX),
    ),
];
#[cfg(target_arch = "aarch64")]
static RANKED: [(Features, Option<&Prepared>); 2] = [
    (
        VG_AES_GCM_SEAL_WITH_POWERS_AES_SHA3_FEATURES,
        Some(&PREPARED_AES_SHA3),
    ),
    (VG_AES_GCM_SEAL_AES_FEATURES, Some(&PREPARED_AES)),
];

/// The family of instances with powers a key uses on a CPU with the
/// features `f`: that of the first implementation in `RANKED` the CPU
/// runs, if it has one and the CPU has the features of all its functions.
#[cfg(any(
    all(target_arch = "x86_64", feature = "alloc"),
    target_arch = "aarch64"
))]
fn prepared(f: Features) -> Option<&'static Prepared> {
    let (_, p) = RANKED.iter().find(|(need, _)| f.contains(*need))?;
    p.filter(|p| f.contains(p.features))
}

/// Why an AES-GCM operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The nonce is empty.
    InvalidNonceLength,
    /// The plaintext or ciphertext is longer than `2^36 − 32` bytes.
    InvalidTextLength,
    /// The additional data is longer than `2^61 − 1` bytes.
    InvalidAadLength,
    /// The tag does not match: the ciphertext, the additional data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
    /// [`AesGcmEncryptor::update_aad`] or [`AesGcmDecryptor::update_aad`]
    /// was called after `update`: GCM authenticates all of the additional
    /// data before the text.
    AadAfterText,
    /// The output of [`AesGcm::encrypt`] is not as long as the plaintext.
    InvalidOutputLength,
    /// More than [`AesGcm::MAX_PIECES`] pieces of plaintext for
    /// [`AesGcm::encrypt`].
    TooManyPieces,
}

crate::error::impl_error! {
    Error {
        InvalidNonceLength => "AES-GCM nonce is empty",
        InvalidTextLength => "AES-GCM text is too long",
        InvalidAadLength => "AES-GCM additional data is too long",
        TagMismatch => "AES-GCM tag does not match",
        AadAfterText => "AES-GCM additional data after the text",
        InvalidOutputLength => "AES-GCM output is not as long as the plaintext",
        TooManyPieces => "too many pieces of AES-GCM plaintext",
    }
}

/// `len + n`, if it is at most `max`.
fn add_len(len: u64, n: usize, max: u64) -> Result<u64, ()> {
    match len.checked_add(n as u64) {
        Some(total) if total <= max => Ok(total),
        _ => Err(()),
    }
}

/// Checks that a nonce is not empty (§5.2.1.1; it is shorter than `2^61`
/// bytes, as no buffer is that long).
fn check_nonce(nonce: &[u8]) -> Result<(), Error> {
    if nonce.is_empty() {
        return Err(Error::InvalidNonceLength);
    }
    Ok(())
}

/// Fails to compile unless `N` is between 4 and 16 bytes, inclusive.
macro_rules! assert_tag_length {
    ($n:expr) => {
        const {
            assert!(
                matches!($n, 4..=16),
                "an AES-GCM tag is between 4 and 16 bytes long"
            )
        }
    };
}

/// An AES-GCM key: its key context (the AES key schedule and the hash
/// subkey `H`). Its [`encrypt_in_place`](Self::encrypt_in_place) and
/// [`decrypt_in_place`](Self::decrypt_in_place) (or
/// [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated)) are the
/// one-shot AEAD; [`encryptor`](Self::encryptor) and
/// [`decryptor`](Self::decryptor) start incremental ones.
#[derive(Clone)]
// On x86-64 the key context, with the powers, is the first field, aligned
// to a cache line, so that the `_prepared` variants' reads of it do not
// cross cache lines, as some would at 8 bytes' alignment. Elsewhere it is
// the first field too: after a pointer, on x86 its offset in a
// 4-byte-aligned value left the compiler unable to clear it with aligned
// 16-byte stores in `new`, and it called `memset` instead (4–5% slower
// `new` on Zen 3).
#[cfg_attr(all(target_arch = "x86_64", feature = "alloc"), repr(C, align(64)))]
#[cfg_attr(not(all(target_arch = "x86_64", feature = "alloc")), repr(C))]
pub struct AesGcm {
    /// The key context `vg_aes_gcm_init` writes (`VG.Spec.Gcm.KeyRepr`),
    /// with the powers of the hash subkey after it on x86-64 (`KeyCtx`):
    /// its first `written()` bytes, which `new` writes; the rest is never
    /// read.
    ctx: MaybeUninit<KeyCtx>,
    rounds: usize,
    /// The family of instances with powers it calls in place of the
    /// dispatchers of the functions it has (`prepared`), if any; on x86-64,
    /// `ctx` then holds the powers.
    #[cfg(any(
        all(target_arch = "x86_64", feature = "alloc"),
        target_arch = "aarch64"
    ))]
    prepared: Option<&'static Prepared>,
    /// On AArch64, the powers of the hash subkey (`VG.Spec.Gcm.Powers8Repr`)
    /// that `new` stores if it has `_with_powers` instances (`prepared`),
    /// which read them; zero otherwise.
    #[cfg(target_arch = "aarch64")]
    powers: Ctx,
}

impl Drop for AesGcm {
    /// Wipes the key context, with the powers.
    fn drop(&mut self) {
        // SAFETY: `self.ctx` is valid for writes of its `written()` bytes (at
        // most `size_of::<KeyCtx>()`), and lies outside `zeroize_raw`'s frame.
        unsafe { zeroize_raw(self.ctx.as_mut_ptr().cast(), self.written()) };
        #[cfg(target_arch = "aarch64")]
        zeroize(&mut self.powers);
    }
}

impl AesGcm {
    /// The size of a full tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Prepares `key`, which must be 16, 24 or 32 bytes long (AES-128,
    /// AES-192 or AES-256).
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut k = AesGcm {
            ctx: MaybeUninit::uninit(),
            rounds: key.len() / 4 + 6,
            #[cfg(any(
                all(target_arch = "x86_64", feature = "alloc"),
                target_arch = "aarch64"
            ))]
            prepared: prepared(detected()),
            #[cfg(target_arch = "aarch64")]
            powers: [0; size_of::<Ctx>() / 8],
        };
        // Only the key context of `vg_aes_gcm_init` is cleared first (`key`
        // reads it); `prepare` writes its proven `written` bytes of powers,
        // and the bytes after them are never read.
        // SAFETY: `k.ctx` is valid for writes of at least 256 bytes.
        unsafe { k.ctx.as_mut_ptr().cast::<[u64; 32]>().write([0; 32]) };
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32; `k.ctx` is valid for reads and writes of 256 bytes. They
        // are distinct objects, so they do not overlap each other or anything
        // on the stack, or wrap around the end of the address space. The
        // dispatcher calls only an implementation the CPU has the features
        // of.
        unsafe { vg_aes_gcm_init_auto(key.as_ptr(), key.len(), k.ctx.as_mut_ptr().cast()) };
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        if let Some(p) = k.prepared {
            k.prepare(p.prepare);
        }
        #[cfg(target_arch = "aarch64")]
        if k.prepared.is_some() {
            k.store_powers();
        }
        Ok(k)
    }

    /// The key context of `vg_aes_gcm_init`, which the plain instances read.
    #[inline(always)]
    fn key(&self) -> &[u64; 32] {
        // SAFETY: `new` writes the first 256 bytes of `self.ctx`.
        unsafe { &*self.ctx.as_ptr().cast::<[u64; 32]>() }
    }

    /// The bytes of `self.ctx` that `new` writes, and `drop` wipes.
    #[inline(always)]
    fn written(&self) -> usize {
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        return self.prepared.map_or(size_of::<[u64; 32]>(), |p| p.written);
        #[cfg(not(all(target_arch = "x86_64", feature = "alloc")))]
        return size_of::<KeyCtx>();
    }

    /// Computes the powers of the hash subkey into `self.ctx`, after its key
    /// context, with `prepare`, the key setup of `self.prepared`.
    #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
    fn prepare(&mut self, prepare: Prepare) {
        // SAFETY: `self.ctx` is valid for reads and writes of 1024 bytes,
        // and overlaps nothing on the stack; its first 256 bytes are the key
        // context of `vg_aes_gcm_init` (`VG.Spec.Gcm.KeyRepr`), which
        // `vg_aes_gcm_prepare` keeps. The CPU has its features (`prepared`).
        unsafe { prepare(self.ctx.as_mut_ptr()) };
    }

    /// Computes the powers of the hash subkey of the key context into
    /// `self.powers`, with `vg_aes_gcm_store_powers_aes`
    /// (`VG.Spec.Gcm.storePowersContract`: `Powers8Repr` of the context's
    /// `ctxH`, which the `_with_powers` instances require).
    #[cfg(target_arch = "aarch64")]
    fn store_powers(&mut self) {
        let ctx: *const [u64; 32] = self.key();
        // SAFETY: `ctx`, the key context, is valid for reads of 256 bytes
        // (`new` wrote them before calling this), and `self.powers` for
        // writes of 128; they are distinct fields, so they do not overlap
        // each other or anything on the stack, or wrap around the end of the
        // address space. The CPU has the features of `self.prepared`, which
        // include `vg_aes_gcm_store_powers_aes`'s (`prepared`).
        unsafe { vg_aes_gcm_store_powers_aes(ctx, &mut self.powers) };
    }

    /// GCM-AE (§7.1): encrypts `data` in place under `nonce`, and returns
    /// the 16-byte tag authenticating the ciphertext and `aad`. A caller that
    /// wants a shorter tag truncates it (keeping its first bytes), and
    /// decrypts with [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated).
    ///
    /// The nonce may have any nonzero length; 12 bytes is the recommended
    /// (and fastest) one. A nonce must never be used twice with the same key.
    pub fn encrypt_in_place(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<Block, Error> {
        // Check the lengths before encrypting anything.
        check_nonce(nonce)?;
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        // On AArch64, the powers, through `seal_prepared`.
        #[cfg(target_arch = "aarch64")]
        match self.prepared {
            Some(p) => return Ok(self.seal_prepared(p, nonce, aad, data)),
            None => no_powers(),
        }
        let mut tag: Block = [0; 16];
        // On x86-64, the `_prepared` instance, on the context with the
        // powers.
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        if let Some(p) = self.prepared {
            // SAFETY: as below, with `self.ctx` followed by the powers
            // `vg_aes_gcm_prepare` wrote for the same key (`AesGcm::new`),
            // valid for reads of 1024 bytes in all. The CPU has the features
            // of `p` (`prepared`).
            unsafe {
                (p.seal)(
                    self.ctx.as_ptr(),
                    self.rounds,
                    nonce.as_ptr(),
                    nonce.len(),
                    aad.as_ptr(),
                    aad.len(),
                    data.as_mut_ptr(),
                    data.len(),
                    &mut tag,
                )
            };
            return Ok(tag);
        }
        // SAFETY: `self.key()` is the key context `vg_aes_gcm_init` wrote for
        // `self.rounds` (10, 12 or 14) rounds (every implementation writes
        // the same one), valid for reads of 256 bytes; `nonce` and `aad` are
        // valid for reads and `data` for reads and writes of their lengths,
        // and `tag` (a local) for reads and writes of 16 bytes. They are
        // distinct objects (`data` a unique borrow), so the writable ones
        // overlap nothing else, nor anything on the stack, and none wraps
        // around the end of the address space. The dispatcher calls only an
        // implementation the CPU has the features of.
        unsafe {
            vg_aes_gcm_seal_auto(
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                &mut tag,
            )
        };
        Ok(tag)
    }

    /// GCM-AD (§7.2): if the 16-byte `tag` authenticates the ciphertext in
    /// `data` and `aad` under `nonce`, decrypts `data` in place. Otherwise
    /// returns an error and leaves `data` unchanged.
    ///
    /// A protocol that truncates the tag uses
    /// [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated).
    pub fn decrypt_in_place(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        self.decrypt_in_place_truncated(nonce, aad, data, tag)
    }

    /// GCM-AD (§7.2) with a tag truncated to `N` bytes: if `tag` is the
    /// first `N` bytes of the tag of the ciphertext in `data` and `aad` under
    /// `nonce`, decrypts `data` in place. Otherwise returns an error and
    /// leaves `data` unchanged.
    ///
    /// `N` must be between 4 and 16, inclusive; any
    /// other length is an error when the call is compiled. It is a type
    /// parameter, fixed in the caller's code, so that it cannot come from the message: see
    /// the [module documentation](self#tags). SP 800-38D Appendix C
    /// restricts 4- and 8-byte tags to applications that bound the length of
    /// the messages and the number of decryptions under one key.
    pub fn decrypt_in_place_truncated<const N: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; N],
    ) -> Result<(), Error> {
        assert_tag_length!(N);
        self.open(nonce, aad, data, tag)
    }

    /// GCM-AD (§7.2) with `tag`, of a length between 4 and 16 (which the
    /// callers check at compile time; `vg_aes_gcm_open` rejects any other).
    fn open(&self, nonce: &[u8], aad: &[u8], data: &mut [u8], tag: &[u8]) -> Result<(), Error> {
        check_nonce(nonce)?;
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        // On x86-64, through `open_with`: on Emerald Rapids, an inline call
        // as in `encrypt_in_place` made every open about 5 ns slower.
        #[cfg(target_arch = "x86_64")]
        return self.open_with(data, tag, nonce, aad);
        // On AArch64, as `encrypt_in_place` there.
        #[cfg(target_arch = "aarch64")]
        if let Some(p) = self.prepared {
            return self.open_prepared(p, nonce, aad, data, tag);
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            // SAFETY: as in `encrypt_in_place`, with the received tag `tag`
            // valid for reads of its length.
            let ok = unsafe {
                vg_aes_gcm_open_auto(
                    self.key(),
                    self.rounds,
                    nonce.as_ptr(),
                    nonce.len(),
                    aad.as_ptr(),
                    aad.len(),
                    data.as_mut_ptr(),
                    data.len(),
                    tag.as_ptr(),
                    tag.len(),
                )
            };
            // `open`'s contract leaves `data` as it was unless it returns 1.
            if ok == 1 {
                Ok(())
            } else {
                Err(Error::TagMismatch)
            }
        }
    }

    /// On x86-64, `open`'s call. Its arguments come in the order that puts
    /// on its stack (`nonce.len()`, `aad`) only what `open` takes in
    /// registers, so each is loaded into a register by itself: passed as
    /// `open` takes them, the three on its stack were what `open` takes on
    /// its own, and the compiler copied two of them with one 16-byte load,
    /// which was not forwarded from the caller's two 8-byte stores (5–11%
    /// slower opens of up to 255 bytes on Zen 3, 4 and 5). It reads
    /// `self.prepared` itself for the same reason.
    #[cfg(target_arch = "x86_64")]
    #[inline(never)]
    fn open_with(
        &self,
        data: &mut [u8],
        tag: &[u8],
        nonce: &[u8],
        aad: &[u8],
    ) -> Result<(), Error> {
        // SAFETY: as in `encrypt_in_place`, with the received tag `tag`
        // valid for reads of its length: the `_prepared` instance on the
        // context with the powers, or the dispatcher on the key context.
        let ok = unsafe {
            #[cfg(feature = "alloc")]
            if let Some(p) = self.prepared {
                (p.open)(
                    self.ctx.as_ptr(),
                    self.rounds,
                    nonce.as_ptr(),
                    nonce.len(),
                    aad.as_ptr(),
                    aad.len(),
                    data.as_mut_ptr(),
                    data.len(),
                    tag.as_ptr(),
                    tag.len(),
                )
            } else {
                self.open_auto(nonce, aad, data, tag)
            }
            #[cfg(not(feature = "alloc"))]
            self.open_auto(nonce, aad, data, tag)
        };
        // `open`'s contract leaves `data` as it was unless it returns 1.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }

    /// On x86-64, `vg_aes_gcm_open_auto` on the key context, for
    /// `open_with`.
    ///
    /// # Safety
    ///
    /// `vg_aes_gcm_open`'s for `data` and `tag`, as `open_with` has them.
    #[cfg(target_arch = "x86_64")]
    #[inline(always)]
    unsafe fn open_auto(&self, nonce: &[u8], aad: &[u8], data: &mut [u8], tag: &[u8]) -> u32 {
        // SAFETY: the caller's. The dispatcher calls only an implementation
        // the CPU has the features of.
        unsafe {
            vg_aes_gcm_open_auto(
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag.as_ptr(),
                tag.len(),
            )
        }
    }

    /// GCM-AD (§7.2), out of place: if the 16-byte `tag` authenticates
    /// `ciphertext` and `aad` under `nonce`, writes the plaintext to `out`,
    /// which must be exactly as long as `ciphertext`. Otherwise returns an
    /// error, having written zeros to `out` if the tag was wrong (and left it
    /// as it was if a length was).
    ///
    /// A protocol that truncates the tag uses
    /// [`decrypt_truncated`](Self::decrypt_truncated).
    pub fn decrypt(
        &self,
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8; 16],
        out: &mut [u8],
    ) -> Result<(), Error> {
        self.decrypt_truncated(nonce, aad, ciphertext, tag, out)
    }

    /// [`decrypt`](Self::decrypt) with a tag truncated to `N` bytes, as
    /// [`decrypt_in_place_truncated`](Self::decrypt_in_place_truncated)
    /// takes it.
    pub fn decrypt_truncated<const N: usize>(
        &self,
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8; N],
        out: &mut [u8],
    ) -> Result<(), Error> {
        assert_tag_length!(N);
        if out.len() != ciphertext.len() {
            return Err(Error::InvalidOutputLength);
        }
        check_nonce(nonce)?;
        add_len(0, out.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        self.open_to(nonce, aad, ciphertext, out, tag)
    }

    /// `vg_aes_gcm_open_to`, which writes zeros to `out` if the tag is wrong,
    /// on every architecture. On AArch64, a key with `_with_powers` instances
    /// copies the ciphertext and calls them instead (`open_to_copy`), as
    /// `encrypt` does there (`seal_pieces_prepared`): there is no
    /// `_with_powers` instance of `vg_aes_gcm_open_to`.
    fn open_to(
        &self,
        nonce: &[u8],
        aad: &[u8],
        src: &[u8],
        out: &mut [u8],
        tag: &[u8],
    ) -> Result<(), Error> {
        #[cfg(target_arch = "aarch64")]
        if self.prepared.is_some() {
            return self.open_to_copy(nonce, aad, src, out, tag);
        }
        // SAFETY: as in `encrypt_in_place`, with `src` and the received tag
        // `tag` valid for reads, and `out` for reads and writes, of their
        // lengths, `out` as long as `src`. `out` is a unique borrow, so it
        // overlaps neither `src` nor any other argument. On x86-64, the
        // `_prepared` instance reads the context with the powers.
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        if let Some(p) = self.prepared {
            let ok = unsafe {
                (p.open_to)(
                    self.ctx.as_ptr(),
                    self.rounds,
                    nonce.as_ptr(),
                    nonce.len(),
                    aad.as_ptr(),
                    aad.len(),
                    src.as_ptr(),
                    src.len(),
                    out.as_mut_ptr(),
                    out.len(),
                    tag.as_ptr(),
                    tag.len(),
                )
            };
            return if ok == 1 {
                Ok(())
            } else {
                Err(Error::TagMismatch)
            };
        }
        // SAFETY: as above, with the key context. The dispatcher calls only
        // an implementation the CPU has the features of.
        let ok = unsafe {
            vg_aes_gcm_open_to_auto(
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                src.as_ptr(),
                src.len(),
                out.as_mut_ptr(),
                out.len(),
                tag.as_ptr(),
                tag.len(),
            )
        };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }

    /// On AArch64, for a key with `_with_powers` instances: the ciphertext
    /// copied to `out` and decrypted there, and `out` zeroed if the tag is
    /// wrong, as `vg_aes_gcm_open_to` does.
    #[cfg(target_arch = "aarch64")]
    fn open_to_copy(
        &self,
        nonce: &[u8],
        aad: &[u8],
        src: &[u8],
        out: &mut [u8],
        tag: &[u8],
    ) -> Result<(), Error> {
        out.copy_from_slice(src);
        let r = self.open(nonce, aad, out, tag);
        if r.is_err() {
            out.fill(0);
        }
        r
    }

    /// The most pieces [`encrypt`](Self::encrypt) takes a plaintext in.
    pub const MAX_PIECES: usize = 64;

    /// GCM-AE (§7.1), out of place: encrypts the plaintext made of the
    /// pieces `plaintext`, in order, under `nonce` into `out`, which must be
    /// exactly as long as they are in all, and returns the 16-byte tag
    /// authenticating the ciphertext and `aad`. A plaintext in one buffer is
    /// one piece (`&[buf]`); there may be at most
    /// [`MAX_PIECES`](Self::MAX_PIECES). The nonce is as for
    /// [`encrypt_in_place`](Self::encrypt_in_place).
    pub fn encrypt(
        &self,
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[&[u8]],
        out: &mut [u8],
    ) -> Result<Block, Error> {
        if plaintext.len() > Self::MAX_PIECES {
            return Err(Error::TooManyPieces);
        }
        check_nonce(nonce)?;
        let mut len = 0;
        for p in plaintext {
            len = add_len(len, p.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        }
        if len != out.len() as u64 {
            return Err(Error::InvalidOutputLength);
        }
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        #[cfg(target_arch = "aarch64")]
        if let Some(p) = self.prepared {
            return Ok(self.seal_pieces_prepared(p, nonce, aad, plaintext, out));
        }
        // The descriptors of the pieces, as `vg_aes_gcm_seal_gather` takes
        // them: each its address and its length. Only the first
        // `plaintext.len()` are written, and the function reads only those.
        let mut descs = [const { MaybeUninit::<[usize; 2]>::uninit() }; Self::MAX_PIECES];
        for (d, p) in descs.iter_mut().zip(plaintext) {
            d.write([p.as_ptr() as usize, p.len()]);
        }
        let src: *const [usize; 2] = descs.as_ptr().cast();
        // The gathering seals every shape of pieces.
        let mut tag: Block = [0; 16];
        // SAFETY: as in `encrypt_in_place`, with `out` valid for reads and
        // writes of `out.len()` bytes; `src` points to `plaintext.len()`
        // initialized descriptors (in `descs`, a local), each the address
        // and the length of a piece valid for reads, which are `out.len()`
        // bytes in all. The pieces and the descriptors are read only, and
        // overlap neither `out` (a unique borrow) nor `tag`, nor anything on
        // the stack the function uses. On x86-64, the `_prepared` instance
        // reads the context with the powers.
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        if let Some(p) = self.prepared {
            unsafe {
                (p.seal_gather)(
                    self.ctx.as_ptr(),
                    self.rounds,
                    nonce.as_ptr(),
                    nonce.len(),
                    aad.as_ptr(),
                    aad.len(),
                    src,
                    plaintext.len(),
                    out.as_mut_ptr(),
                    out.len(),
                    &mut tag,
                )
            };
            return Ok(tag);
        }
        // SAFETY: as above, with the key context. The dispatcher calls only
        // an implementation the CPU has the features of.
        unsafe {
            vg_aes_gcm_seal_gather_auto(
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                src,
                plaintext.len(),
                out.as_mut_ptr(),
                out.len(),
                &mut tag,
            )
        };
        Ok(tag)
    }

    /// Starts encrypting a message under this key and `nonce` (of any
    /// nonzero length; 12 bytes is the recommended one). A nonce must never
    /// be used twice with the same key.
    pub fn encryptor(&self, nonce: &[u8]) -> Result<AesGcmEncryptor<'_>, Error> {
        Ok(AesGcmEncryptor {
            stream: Stream::new(self, nonce)?,
        })
    }

    /// Starts decrypting a message under this key and `nonce`. Its
    /// [`update`](AesGcmDecryptor::update) returns plaintext that has not
    /// been authenticated until its [`finalize`](AesGcmDecryptor::finalize)
    /// succeeds.
    pub fn decryptor(&self, nonce: &[u8]) -> Result<AesGcmDecryptor<'_>, Error> {
        Ok(AesGcmDecryptor {
            stream: Stream::new(self, nonce)?,
        })
    }
}

/// On AArch64, marks the path of a backend without `_with_powers`
/// instances unlikely, so that the call of `seal_prepared` falls through
/// (measured on Neoverse N2: a branch around it cost 1% at 15 bytes).
#[cfg(target_arch = "aarch64")]
#[cold]
#[inline(never)]
fn no_powers() {}

/// On AArch64, the calls of the `_with_powers` instances.
#[cfg(target_arch = "aarch64")]
impl AesGcm {
    /// `encrypt_in_place` with the `_with_powers` instances `p` and the
    /// powers.
    #[inline]
    fn seal_prepared(&self, p: &Prepared, nonce: &[u8], aad: &[u8], data: &mut [u8]) -> Block {
        let mut tag: Block = [0; 16];
        let seal = p.seal;
        // SAFETY: as in `encrypt_in_place`, with the powers of the same key,
        // `self.powers`, the 128 bytes `store_powers` wrote from the key
        // context, which overlap nothing the call writes. The CPU has the
        // features of `p`, the key's `self.prepared` (`prepared`).
        unsafe {
            seal(
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                &mut tag,
                &self.powers,
            )
        };
        tag
    }

    /// `open` with the `_with_powers` instances `p` and the powers.
    #[inline]
    fn open_prepared(
        &self,
        p: &Prepared,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8],
    ) -> Result<(), Error> {
        let open = p.open;
        // SAFETY: as in `seal_prepared`, with the received tag `tag` valid
        // for reads of its length.
        let ok = unsafe {
            open(
                self.key(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag.as_ptr(),
                tag.len(),
                &self.powers,
            )
        };
        // As in `open`.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }

    /// `encrypt` with the `_with_powers` instances `p`: copies the pieces
    /// `plaintext` to `out`, one after the other (as
    /// `vg_aes_gcm_seal_gather` does), and seals them there with
    /// `seal_prepared`. Which bytes it copies where depends only on the
    /// pieces' lengths (whose sum `encrypt` checked is `out.len()`).
    #[inline(never)]
    fn seal_pieces_prepared(
        &self,
        p: &Prepared,
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[&[u8]],
        out: &mut [u8],
    ) -> Block {
        let mut rest = &mut *out;
        for piece in plaintext {
            let (dst, tail) = rest.split_at_mut(piece.len());
            dst.copy_from_slice(piece);
            rest = tail;
        }
        self.seal_prepared(p, nonce, aad, out)
    }
}

/// The state of an incremental encryption or decryption (`DECRYPT`), which
/// [`AesGcmEncryptor`] and [`AesGcmDecryptor`] wrap: the key, the streaming
/// state, and the lengths absorbed so far.
#[derive(Clone)]
struct Stream<'a, const DECRYPT: bool> {
    key: &'a AesGcm,
    /// The streaming state `vg_aes_gcm_stream_init` writes and the other
    /// functions update (`VG.Spec.Gcm.StreamRepr`).
    state: [u64; 10],
    aad_len: u64,
    text_len: u64,
    /// Whether [`update`](Self::update) has been called.
    in_text: bool,
}

impl<const DECRYPT: bool> Drop for Stream<'_, DECRYPT> {
    /// Wipes the streaming state (the key wipes itself).
    fn drop(&mut self) {
        zeroize(&mut self.state);
    }
}

impl<'a, const DECRYPT: bool> Stream<'a, DECRYPT> {
    /// Starts a message under `key` and `nonce`.
    fn new(key: &'a AesGcm, nonce: &[u8]) -> Result<Self, Error> {
        check_nonce(nonce)?;
        let mut s = Stream {
            key,
            state: [0; 10],
            aad_len: 0,
            text_len: 0,
            in_text: false,
        };
        // SAFETY: `key.key()` is a key context (as in
        // `AesGcm::encrypt_in_place`), valid for reads of 256 bytes, `nonce`
        // for reads of `nonce.len()`, and `s.state` for reads and writes of
        // 80. They are distinct objects, so the writable one overlaps nothing
        // else, nor anything on the stack, and none wraps around. The
        // dispatcher calls only an implementation the CPU has the features
        // of.
        unsafe {
            vg_aes_gcm_stream_init_auto(key.key(), nonce.as_ptr(), nonce.len(), &mut s.state)
        };
        Ok(s)
    }

    /// Absorbs more additional data, which must all come before the text.
    fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        if self.in_text {
            return Err(Error::AadAfterText);
        }
        let aad_len =
            add_len(self.aad_len, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        // SAFETY: as in `new`; `self.state` represents a message with
        // `self.aad_len` bytes of additional data and no text yet.
        unsafe {
            vg_aes_gcm_stream_aad_auto(
                self.key.key(),
                &mut self.state,
                self.aad_len,
                aad.as_ptr(),
                aad.len(),
            )
        };
        self.aad_len = aad_len;
        Ok(())
    }

    /// Encrypts (or, if `DECRYPT`, decrypts) the next `data.len()` bytes of
    /// the text in place.
    fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        let text_len =
            add_len(self.text_len, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        self.in_text = true;
        let (rounds, d, len) = (self.key.rounds, data.as_mut_ptr(), data.len());
        let (state, aad_len, done) = (&mut self.state, self.aad_len, self.text_len);
        // SAFETY: as in `new`, with `data` valid for reads and writes of
        // `data.len()` bytes (a unique borrow, so it overlaps nothing else);
        // `self.state` represents a message with `self.aad_len` bytes of
        // additional data and `self.text_len` of text. On x86-64, the
        // `_prepared` instance reads the context with the powers (as in
        // `AesGcm::encrypt_in_place`).
        unsafe {
            #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
            if let Some(p) = self.key.prepared {
                let f = if DECRYPT {
                    p.stream_decrypt
                } else {
                    p.stream_encrypt
                };
                f(self.key.ctx.as_ptr(), rounds, state, aad_len, done, d, len);
                self.text_len = text_len;
                return Ok(());
            }
            let ctx = self.key.key();
            if DECRYPT {
                vg_aes_gcm_stream_decrypt_auto(ctx, rounds, state, aad_len, done, d, len);
            } else {
                vg_aes_gcm_stream_encrypt_auto(ctx, rounds, state, aad_len, done, d, len);
            }
        };
        self.text_len = text_len;
        Ok(())
    }
}

impl Stream<'_, false> {
    /// Finishes the message and returns its 16-byte tag.
    fn finish(mut self) -> Block {
        let mut tag: Block = [0; 16];
        // SAFETY: as in `update`, with `tag` (a local) valid for reads and
        // writes of 16 bytes. `update_aad` and `update` checked the lengths
        // (§5.2.1.1).
        unsafe {
            vg_aes_gcm_stream_finish_auto(
                self.key.key(),
                self.key.rounds,
                &mut self.state,
                self.aad_len,
                self.text_len,
                &mut tag,
            )
        };
        tag
    }
}

impl Stream<'_, true> {
    /// Finishes the message and checks the received prefix in constant time.
    /// Callers check at compile time that its length is between 4 and 16.
    fn verify(mut self, tag: &[u8]) -> Result<(), Error> {
        // SAFETY: as in `finish`, with the received tag `tag` valid for
        // reads of its length.
        let ok = unsafe {
            vg_aes_gcm_stream_verify_auto(
                self.key.key(),
                self.key.rounds,
                &mut self.state,
                self.aad_len,
                self.text_len,
                tag.as_ptr(),
                tag.len(),
            )
        };
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

/// An incremental AES-GCM encryption, from [`AesGcm::encryptor`]: the
/// additional data with [`update_aad`](Self::update_aad), then the plaintext
/// with [`update`](Self::update), in pieces of any length, and the tag from
/// [`finalize`](Self::finalize).
///
/// It borrows its [`AesGcm`], so a key encrypts many messages without
/// expanding it again.
#[derive(Clone)]
pub struct AesGcmEncryptor<'a> {
    stream: Stream<'a, false>,
}

impl AesGcmEncryptor<'_> {
    /// Absorbs more additional data. All of it must come before the
    /// plaintext.
    pub fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        self.stream.update_aad(aad)
    }

    /// Encrypts the next `data.len()` bytes of the plaintext in place.
    pub fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        self.stream.update(data)
    }

    /// Finishes the message and returns its full 16-byte tag. A protocol
    /// that sends a shorter tag sends its first bytes. GCM leaves no
    /// buffered text to return.
    pub fn finalize(self) -> Block {
        self.stream.finish()
    }
}

/// An incremental AES-GCM decryption, from [`AesGcm::decryptor`]: the
/// additional data with [`update_aad`](Self::update_aad), then the
/// ciphertext with [`update`](Self::update), in pieces of any length, and
/// the tag checked by [`finalize`](Self::finalize) (16 bytes) or
/// [`finalize_truncated`](Self::finalize_truncated) (a length fixed at
/// compile time: see the [module documentation](self#tags)).
///
/// **[`update`](Self::update) returns plaintext that has not been
/// authenticated yet.** Nothing may act on it before
/// [`finalize`](Self::finalize) (or
/// [`finalize_truncated`](Self::finalize_truncated)) has succeeded. When the
/// whole message fits in memory, [`AesGcm::decrypt_in_place`] checks the tag
/// before it decrypts.
#[derive(Clone)]
pub struct AesGcmDecryptor<'a> {
    stream: Stream<'a, true>,
}

impl AesGcmDecryptor<'_> {
    /// Absorbs more additional data. All of it must come before the
    /// ciphertext.
    pub fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        self.stream.update_aad(aad)
    }

    /// Decrypts the next `data.len()` bytes of the ciphertext in place. The
    /// result is not authenticated until [`finalize`](Self::finalize) (or
    /// [`finalize_truncated`](Self::finalize_truncated)) succeeds.
    pub fn update(&mut self, data: &mut [u8]) -> Result<(), Error> {
        self.stream.update(data)
    }

    /// Finishes the message and checks that `tag` is its 16-byte tag. If
    /// they differ, this fails, and nothing may act on the plaintext
    /// [`update`](Self::update) returned.
    ///
    /// A protocol that truncates the tag uses
    /// [`finalize_truncated`](Self::finalize_truncated).
    pub fn finalize(self, tag: &[u8; 16]) -> Result<(), Error> {
        self.finalize_truncated(tag)
    }

    /// Finishes the message and checks that `tag` is the first `N` bytes of
    /// its tag. If they differ, this fails, and nothing may act on the
    /// plaintext [`update`](Self::update) returned.
    ///
    /// `N` must be between 4 and 16, inclusive; any
    /// other length is an error when the call is compiled. It is a type
    /// parameter, fixed in the caller's code, so that it cannot come from the
    /// message: see the [module documentation](self#tags). SP 800-38D
    /// Appendix C restricts 4- and 8-byte tags to applications that bound the
    /// length of the messages and the number of decryptions under one key.
    pub fn finalize_truncated<const N: usize>(self, tag: &[u8; N]) -> Result<(), Error> {
        assert_tag_length!(N);
        self.stream.verify(tag)
    }
}

#[cfg(test)]
mod tests {
    use super::{AesGcm, Error, InvalidKeyLength, MAX_AAD, MAX_TEXT, add_len};

    /// Encryption and decryption are inverse, for every key size, 12-byte
    /// and other nonces, and texts and additional data of whole and partial
    /// blocks; a modified tag is rejected.
    #[test]
    fn round_trip() {
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let msg: [u8; 67] = core::array::from_fn(|i| (i as u8).wrapping_mul(7));
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&key[..key_len]).unwrap();
            for nonce_len in [1, 12, 16, 17] {
                let nonce = &[0x5a; 17][..nonce_len];
                for len in [0, 1, 16, 31, 64, 67] {
                    let (msg, aad) = (&msg[..len], &msg[..len / 2]);
                    let mut buf = [0u8; 67];
                    let buf = &mut buf[..len];
                    buf.copy_from_slice(msg);
                    let tag = k.encrypt_in_place(nonce, aad, buf).unwrap();
                    assert!(len == 0 || buf != msg);
                    let mut bad = tag;
                    bad[15] ^= 1;
                    assert_eq!(
                        k.decrypt_in_place(nonce, aad, buf, &bad),
                        Err(Error::TagMismatch)
                    );
                    k.decrypt_in_place(nonce, aad, buf, &tag).unwrap();
                    assert_eq!(buf, msg);
                }
            }
        }
    }

    /// One-shot encryption and decryption of long messages agree with the
    /// streaming functions, and a wrong tag leaves the ciphertext as it was.
    #[test]
    fn long_one_shot() {
        let msg: [u8; 4111] = core::array::from_fn(|i| (i * 31 + 7) as u8);
        let aad = [3u8; 21];
        let nonce = [5u8; 12];
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&[0x42; 32][..key_len]).unwrap();
            for len in [255, 256, 257, 511, 512, 529, 1024, 4096, 4111] {
                let mut ct = msg;
                let ct = &mut ct[..len];
                let tag = k.encrypt_in_place(&nonce, &aad, ct).unwrap();
                let mut e = k.encryptor(&nonce).unwrap();
                e.update_aad(&aad).unwrap();
                let mut s = msg;
                e.update(&mut s[..len]).unwrap();
                assert_eq!(&s[..len], &ct[..]);
                assert_eq!(e.finalize(), tag);

                let mut bad = tag;
                bad[0] ^= 0x80;
                let mut buf = msg;
                let buf = &mut buf[..len];
                buf.copy_from_slice(ct);
                assert_eq!(
                    k.decrypt_in_place(&nonce, &aad, buf, &bad),
                    Err(Error::TagMismatch)
                );
                assert_eq!(&buf[..], &ct[..]);
                k.decrypt_in_place(&nonce, &aad, buf, &tag).unwrap();
                assert_eq!(buf, &msg[..len]);
            }
        }
    }

    /// Streaming a long message in three updates, split on and off block
    /// boundaries, agrees with the one-shot functions, in both directions.
    #[test]
    fn long_stream() {
        let msg: [u8; 1100] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        let aad = [6u8; 13];
        let nonce = [8u8; 12];
        let k = AesGcm::new(&[0x24; 16]).unwrap();
        let mut ct = msg;
        let tag = k.encrypt_in_place(&nonce, &aad, &mut ct).unwrap();
        let splits = [
            (0, 1100),
            (1, 300),
            (15, 16),
            (16, 529),
            (17, 1099),
            (255, 256),
            (300, 1100),
            (513, 514),
        ];
        for (a, b) in splits {
            let mut e = k.encryptor(&nonce).unwrap();
            e.update_aad(&aad).unwrap();
            let mut buf = msg;
            let (x, rest) = buf.split_at_mut(a);
            let (y, z) = rest.split_at_mut(b - a);
            e.update(x).unwrap();
            e.update(y).unwrap();
            e.update(z).unwrap();
            assert_eq!(buf, ct);
            assert_eq!(e.finalize(), tag);

            let mut d = k.decryptor(&nonce).unwrap();
            d.update_aad(&aad).unwrap();
            let (x, rest) = buf.split_at_mut(a);
            let (y, z) = rest.split_at_mut(b - a);
            d.update(x).unwrap();
            d.update(y).unwrap();
            d.update(z).unwrap();
            assert_eq!(buf, msg);
            assert_eq!(d.finalize(&tag), Ok(()));
        }
    }

    /// Streaming, with the additional data or the text split at every
    /// point (around block boundaries), agrees with the one-shot functions,
    /// in both directions, with one key for every message.
    #[test]
    fn stream() {
        let key = [7u8; 16];
        let nonce = [9u8; 12];
        let aad: [u8; 40] = core::array::from_fn(|i| i as u8);
        let msg: [u8; 50] = core::array::from_fn(|i| (i as u8).wrapping_mul(13));
        let k = AesGcm::new(&key).unwrap();
        let mut ct = msg;
        let tag = k.encrypt_in_place(&nonce, &aad, &mut ct).unwrap();
        // Every split of one, with the other split in the middle.
        let splits = (0..=aad.len())
            .map(|a| (a, msg.len() / 2))
            .chain((0..=msg.len()).map(|m| (aad.len() / 2, m)));
        for (a, m) in splits {
            let mut e = k.encryptor(&nonce).unwrap();
            e.update_aad(&aad[..a]).unwrap();
            e.update_aad(&aad[a..]).unwrap();
            let mut buf = msg;
            let (x, y) = buf.split_at_mut(m);
            e.update(x).unwrap();
            e.update(y).unwrap();
            assert_eq!(buf, ct);
            assert_eq!(e.finalize(), tag);

            let mut d = k.decryptor(&nonce).unwrap();
            d.update_aad(&aad[..a]).unwrap();
            d.update_aad(&aad[a..]).unwrap();
            let (x, y) = buf.split_at_mut(m);
            d.update(x).unwrap();
            d.update(y).unwrap();
            assert_eq!(buf, msg);
            assert_eq!(d.finalize(&tag), Ok(()));
        }
        // A byte at a time.
        let mut e = k.encryptor(&nonce).unwrap();
        for b in aad.chunks(1) {
            e.update_aad(b).unwrap();
        }
        let mut buf = msg;
        for b in buf.chunks_mut(1) {
            e.update(b).unwrap();
        }
        assert_eq!(buf, ct);
        assert_eq!(e.finalize(), tag);
        // Without text, or without either.
        let mut t = [0u8; 0];
        let tag = k.encrypt_in_place(&nonce, &aad[..5], &mut t).unwrap();
        let mut e = k.encryptor(&nonce).unwrap();
        e.update_aad(&aad[..5]).unwrap();
        assert_eq!(e.finalize(), tag);
        let tag = k.encrypt_in_place(&nonce, &[], &mut t).unwrap();
        let e = k.encryptor(&nonce).unwrap();
        assert_eq!(e.finalize(), tag);
        let d = k.decryptor(&nonce).unwrap();
        assert_eq!(d.finalize(&tag), Ok(()));
    }

    /// A clone continues the message independently of the original.
    #[test]
    fn stream_clone() {
        let k = AesGcm::new(&[1; 24]).unwrap();
        let nonce = [2u8; 12];
        let msg = [3u8; 20];
        let mut ct = msg;
        let tag = k.encrypt_in_place(&nonce, &[4; 8], &mut ct).unwrap();

        let mut e = k.encryptor(&nonce).unwrap();
        e.update_aad(&[4; 8]).unwrap();
        let mut other = e.clone();
        other.update(&mut [0; 1]).unwrap();
        let mut buf = msg;
        e.update(&mut buf).unwrap();
        assert_eq!((buf, e.finalize()), (ct, tag));
        assert_ne!(other.finalize(), tag);

        let mut d = k.decryptor(&nonce).unwrap();
        d.update_aad(&[4; 8]).unwrap();
        let mut other = d.clone();
        other.update(&mut [0; 1]).unwrap();
        let mut buf = ct;
        d.update(&mut buf).unwrap();
        assert_eq!(buf, msg);
        assert_eq!(d.finalize(&tag), Ok(()));
        assert_eq!(other.finalize(&tag), Err(Error::TagMismatch));
    }

    /// A tag truncated to `N` bytes: its first `N` bytes are accepted, one
    /// at a time and streaming, and any other `N` bytes (a bit flipped in
    /// each byte) are rejected, leaving the ciphertext unchanged.
    fn truncated<const N: usize>() {
        let key = [3u8; 16];
        let nonce = [4u8; 12];
        let aad = [5u8; 20];
        let msg: [u8; 37] = core::array::from_fn(|i| i as u8);
        let k = AesGcm::new(&key).unwrap();
        let mut ct = msg;
        let full = k.encrypt_in_place(&nonce, &aad, &mut ct).unwrap();
        let tag: [u8; N] = full[..N].try_into().unwrap();
        let mut buf = ct;
        k.decrypt_in_place_truncated(&nonce, &aad, &mut buf, &tag)
            .unwrap();
        assert_eq!(buf, msg);
        let stream = |tag: &[u8; N]| {
            let mut d = k.decryptor(&nonce).unwrap();
            d.update_aad(&aad).unwrap();
            let mut buf = ct;
            d.update(&mut buf).unwrap();
            assert_eq!(buf, msg);
            d.finalize_truncated(tag)
        };
        assert_eq!(stream(&tag), Ok(()));
        for i in 0..N {
            let mut bad = tag;
            bad[i] ^= 0x80;
            let mut buf = ct;
            assert_eq!(
                k.decrypt_in_place_truncated(&nonce, &aad, &mut buf, &bad),
                Err(Error::TagMismatch)
            );
            assert_eq!(buf, ct);
            assert_eq!(stream(&bad), Err(Error::TagMismatch));
        }
    }

    /// Empty messages, partial blocks, and prepared-context boundaries.
    fn truncated_boundaries<const N: usize>() {
        let key = [3u8; 32];
        let nonce = [4u8; 13];
        let aad = [5u8; 20];
        let msg: [u8; 2057] = core::array::from_fn(|i| i as u8);
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&key[..key_len]).unwrap();
            for nonce_len in [12, 13] {
                let nonce = &nonce[..nonce_len];
                for len in [
                    0, 1, 15, 16, 17, 127, 128, 255, 256, 257, 511, 512, 513, 1023, 1024, 1025,
                    2057,
                ] {
                    let aad = &aad[..if len % 2 == 0 { 0 } else { aad.len() }];
                    let mut ct = msg;
                    let full = k.encrypt_in_place(nonce, aad, &mut ct[..len]).unwrap();
                    let tag: [u8; N] = full[..N].try_into().unwrap();
                    let mut buf = ct;
                    k.decrypt_in_place_truncated(nonce, aad, &mut buf[..len], &tag)
                        .unwrap();
                    assert_eq!(&buf[..len], &msg[..len]);
                    let mut d = k.decryptor(nonce).unwrap();
                    d.update_aad(aad).unwrap();
                    buf = ct;
                    for chunk in buf[..len].chunks_mut(17) {
                        d.update(chunk).unwrap();
                    }
                    d.finalize_truncated(&tag).unwrap();
                    assert_eq!(&buf[..len], &msg[..len]);
                    let mut bad = tag;
                    bad[N - 1] ^= 1;
                    buf = ct;
                    assert_eq!(
                        k.decrypt_in_place_truncated(nonce, aad, &mut buf[..len], &bad),
                        Err(Error::TagMismatch)
                    );
                    assert_eq!(buf, ct);
                }
            }
            let mut empty = [];
            assert_eq!(
                k.decrypt_in_place_truncated(&[], &aad, &mut empty, &[0; N]),
                Err(Error::InvalidNonceLength)
            );
        }
    }

    /// Every supported tag length, including the extensions to §5.2.1.2.
    #[test]
    fn truncated_tags() {
        truncated::<4>();
        truncated::<5>();
        truncated::<6>();
        truncated::<7>();
        truncated::<8>();
        truncated::<9>();
        truncated::<10>();
        truncated::<11>();
        truncated::<12>();
        truncated::<13>();
        truncated::<14>();
        truncated::<15>();
        truncated::<16>();
        truncated_boundaries::<5>();
        truncated_boundaries::<6>();
        truncated_boundaries::<7>();
        truncated_boundaries::<9>();
        truncated_boundaries::<10>();
        truncated_boundaries::<11>();
    }

    /// Out-of-place encryption of a plaintext in pieces matches in-place
    /// encryption, after additional data of whole blocks, of a partial block
    /// and of none, for pieces split on and off block boundaries (empty ones
    /// included), the most pieces, and an empty text; an output of the wrong
    /// length and too many pieces are refused.
    #[test]
    fn out_of_place() {
        let k = AesGcm::new(&[3; 16]).unwrap();
        let nonce = [5u8; 12];
        let msg: [u8; 300] = core::array::from_fn(|i| (i as u8).wrapping_mul(29));
        for aad_len in [0, 5, 16, 20] {
            let aad = &msg[..aad_len];
            for len in [0, 1, 16, 17, 300] {
                let mut want = msg;
                let want_tag = k.encrypt_in_place(&nonce, aad, &mut want[..len]).unwrap();
                let m = &msg[..len];
                let (h, q) = (len / 2, (len / 2 + 16).min(len));
                let one: [&[u8]; 1] = [m];
                let two: [&[u8]; 2] = [&m[..h], &m[h..]];
                let five: [&[u8]; 5] = [&[], &m[..h], &m[h..h], &m[h..q], &m[q..]];
                for pieces in [&one[..], &two, &five] {
                    let mut out = [0u8; 300];
                    let tag = k.encrypt(&nonce, aad, pieces, &mut out[..len]);
                    assert_eq!((&out[..len], tag), (&want[..len], Ok(want_tag)));
                }
            }
        }
        let n = AesGcm::MAX_PIECES;
        let mut want = msg;
        let want_tag = k.encrypt_in_place(&nonce, &[], &mut want[..n]).unwrap();
        let bytes: [&[u8]; AesGcm::MAX_PIECES] = core::array::from_fn(|i| &msg[i..i + 1]);
        let mut out = [0u8; AesGcm::MAX_PIECES];
        let tag = k.encrypt(&nonce, &[], &bytes, &mut out);
        assert_eq!((&out[..], tag), (&want[..n], Ok(want_tag)));
        let empty = [&msg[..0]; AesGcm::MAX_PIECES + 1];
        let tag = k.encrypt(&nonce, &[], &empty, &mut []);
        assert_eq!(tag, Err(Error::TooManyPieces));
        assert_eq!(
            k.encrypt(&nonce, &[], &[], &mut []),
            k.encrypt(&nonce, &[], &[&[]], &mut [])
        );
        let mut out = [0u8; 4];
        let tag = k.encrypt(&nonce, &[], &[&msg[..1], &msg[1..3]], &mut out);
        assert_eq!(tag, Err(Error::InvalidOutputLength));
        let t = [0u8; 16];
        assert_eq!(
            k.decrypt(&nonce, &[], &msg[..3], &t, &mut out),
            Err(Error::InvalidOutputLength)
        );
        assert_eq!(
            k.decrypt(&[], &[], &msg[..4], &t, &mut out),
            Err(Error::InvalidNonceLength)
        );
        assert_eq!(out, [0; 4]);
        assert_eq!(
            k.encrypt(&[], &[], &[&msg[..4]], &mut out),
            Err(Error::InvalidNonceLength)
        );
    }

    #[test]
    fn errors() {
        assert_eq!(AesGcm::new(&[0; 15]).err(), Some(InvalidKeyLength));
        let k = AesGcm::new(&[0; 32]).unwrap();
        let mut buf = [0u8; 3];
        assert_eq!(
            k.encrypt_in_place(&[], &[], &mut buf),
            Err(Error::InvalidNonceLength)
        );
        assert_eq!(
            k.decrypt_in_place(&[], &[], &mut buf, &[0; 16]),
            Err(Error::InvalidNonceLength)
        );
        assert_eq!(
            k.decrypt_in_place(&[0; 12], &[], &mut buf, &[0; 16]),
            Err(Error::TagMismatch)
        );
        assert_eq!(buf, [0; 3]);

        assert_eq!(k.encryptor(&[]).err(), Some(Error::InvalidNonceLength));
        assert_eq!(k.decryptor(&[]).err(), Some(Error::InvalidNonceLength));
        let mut e = k.encryptor(&[0; 12]).unwrap();
        e.update(&mut buf).unwrap();
        assert_eq!(e.update_aad(&[1]), Err(Error::AadAfterText));
        let mut d = k.decryptor(&[0; 12]).unwrap();
        d.update(&mut buf).unwrap();
        assert_eq!(d.update_aad(&[1]), Err(Error::AadAfterText));
        assert_eq!(d.finalize(&[0; 16]), Err(Error::TagMismatch));

        // The length limits (§5.2.1.1), which no test can reach with real
        // buffers.
        assert_eq!(add_len(MAX_TEXT - 1, 1, MAX_TEXT), Ok(MAX_TEXT));
        assert_eq!(add_len(MAX_TEXT, 1, MAX_TEXT), Err(()));
        assert_eq!(add_len(MAX_AAD, 0, MAX_AAD), Ok(MAX_AAD));
        assert_eq!(add_len(u64::MAX, 1, MAX_AAD), Err(()));
        let mut e = k.encryptor(&[0; 12]).unwrap();
        e.stream.text_len = MAX_TEXT;
        assert_eq!(e.update(&mut buf), Err(Error::InvalidTextLength));
        e.stream.aad_len = MAX_AAD;
        e.stream.in_text = false;
        assert_eq!(e.update_aad(&[1]), Err(Error::InvalidAadLength));
        let mut d = k.decryptor(&[0; 12]).unwrap();
        d.stream.text_len = MAX_TEXT;
        assert_eq!(d.update(&mut buf), Err(Error::InvalidTextLength));
        d.stream.aad_len = MAX_AAD;
        assert_eq!(d.update_aad(&[1]), Err(Error::InvalidAadLength));
    }
}
