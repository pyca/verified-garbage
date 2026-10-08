//! AES-GCM (NIST SP 800-38D) with 128-, 192- and 256-bit AES keys.
//!
//! The whole AEAD is verified assembly: `vg_aes_gcm_init` (contract
//! `VG.Spec.Gcm.initContract`) writes the key context (the AES key schedule
//! and the hash subkey `H`), `vg_aes_gcm_seal` and `vg_aes_gcm_open`
//! (`sealContract`, `openContract`) are GCM-AE and GCM-AD (§7), and
//! `vg_aes_gcm_stream_init`, `_aad`, `_encrypt`, `_decrypt`, `_finish` and
//! `_verify` keep a streaming state (`VG.Spec.Gcm.StreamRepr`). `open` and
//! `verify` check the tag, in constant time, and `open` decrypts only if it
//! matches. This module checks the lengths of §5.2.1.1, which the assembly
//! does not, and holds the key context and the state.
//!
//! An [`AesGcm`] is a key: it encrypts and decrypts whole messages at once,
//! and starts incremental ones with [`AesGcm::encryptor`] and
//! [`AesGcm::decryptor`], which borrow it. **An [`AesGcmDecryptor`]'s
//! `update` returns plaintext that has not been authenticated yet**: nothing
//! may act on it before its `finalize` has succeeded. When the whole message
//! fits in memory, [`AesGcm::decrypt_in_place`] checks the tag before it
//! decrypts.
//!
//! [`AesGcm::encrypt`] encrypts out of place, from a plaintext in pieces (a
//! list of slices, such as a record's header and payload, or a single one)
//! into one output buffer: one call of `vg_aes_gcm_seal_gather`
//! (`VG.Spec.Gcm.sealGatherContract`), which reads each piece where it is.
//!
//! # Tags
//!
//! Encryption returns the full 16-byte tag; a protocol that sends a shorter
//! one sends its first bytes. Decryption takes a `&[u8; 16]`
//! ([`AesGcm::decrypt_in_place`], [`AesGcmDecryptor::finalize`]), or, for a
//! protocol that truncates the tag, a `&[u8; N]` whose length `N` is a type
//! parameter ([`AesGcm::decrypt_in_place_truncated`],
//! [`AesGcmDecryptor::finalize_truncated`]): one of the lengths SP 800-38D
//! §5.2.1.2 allows, 4, 8, 12, 13, 14, 15 or 16 bytes, checked at compile
//! time. The length is never taken from a slice, because a slice's length
//! often comes from the message: a protocol that splits a message with
//! `msg.split_at(msg.len().saturating_sub(16))` would, given a 4-byte
//! message, check an empty ciphertext against a 4-byte tag, which an
//! attacker forges with probability 2⁻³² instead of 2⁻¹²⁸. Tags of 4 and 8
//! bytes are only for the applications of SP 800-38D Appendix C, which
//! bounds the lengths of the messages and the number of decryptions under
//! one key.
//!
//! The functions are emitted once for each implementation of AES
//! (`vg_aes_expand_key` and `vg_aes_ctr32`) and of `vg_ghash` they call,
//! which have the same contracts: on x86-64, CPUs with AES-NI and SSSE3 run
//! the `_aesni` instances (with `vg_aes_ctr32_aesni`), CPUs with PCLMULQDQ
//! and SSSE3 the `_pclmul` ones (with `vg_ghash_pclmul`), and CPUs with all
//! three the `_aesni_pclmul` ones; CPUs with VAES or VPCLMULQDQ (and AVX2)
//! run, instead of AES-NI's or PCLMULQDQ's, the `_vaes` or `_vpclmul`
//! instances (with `vg_aes_ctr32_vaes` and `vg_ghash_vpclmul`, sixteen and
//! eight blocks at a time in 256-bit registers), or those of the pairs
//! (`_vaes_vpclmul`, `_vaes_pclmul`, `_aesni_vpclmul`), and CPUs with VAES,
//! VPCLMULQDQ, AVX512F and AVX512BW the `_vaes_vpclmul_avx512` ones, whose
//! interleaved counter mode and GHASH work in 512-bit registers, and CPUs
//! with AES-NI, PCLMULQDQ and AVX but neither VAES nor VPCLMULQDQ the
//! `_aesni_pclmul_avx` ones, which interleave them in 128-bit registers
//! (where the `_aesni_pclmul` ones make two passes); likewise on x86, where
//! AES-NI needs no SSSE3 (and the 256-bit instances are not built); on AArch64, CPUs with the AES and PMULL extensions (which Rust's
//! `aes` feature stands for together) run the `_aes` ones (with
//! `vg_aes_ctr32_aes` and `vg_ghash_aes`).
//!
//! On x86-64, the `_vaes_vpclmul_avx512` instances also have `_precomputed`
//! ones (`VG.Spec.Gcm.PowersRepr`), whose interleaved loops read the powers
//! `H¹ … H⁴⁸` of the hash subkey from a larger key context, which
//! `vg_aes_gcm_init_precomputed` writes, instead of computing them on every
//! call. A key computes it once, after it has encrypted or decrypted
//! `POWERS_AFTER` messages (or streaming updates) long enough to gain from
//! it, so that one used for a few messages never pays for it.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::arch::gcm::vg_aes_gcm_seal_gather;
#[cfg(target_arch = "aarch64")]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_AES_FEATURES, vg_aes_gcm_init_aes, vg_aes_gcm_open_aes, vg_aes_gcm_seal_aes,
    vg_aes_gcm_seal_gather_aes, vg_aes_gcm_stream_aad_aes, vg_aes_gcm_stream_decrypt_aes,
    vg_aes_gcm_stream_encrypt_aes, vg_aes_gcm_stream_finish_aes, vg_aes_gcm_stream_init_aes,
    vg_aes_gcm_stream_verify_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_AESNI_FEATURES, VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES,
    VG_AES_GCM_SEAL_PCLMUL_FEATURES, vg_aes_gcm_init_aesni, vg_aes_gcm_init_aesni_pclmul,
    vg_aes_gcm_init_pclmul, vg_aes_gcm_open_aesni, vg_aes_gcm_open_aesni_pclmul,
    vg_aes_gcm_open_pclmul, vg_aes_gcm_seal_aesni, vg_aes_gcm_seal_aesni_pclmul,
    vg_aes_gcm_seal_gather_aesni, vg_aes_gcm_seal_gather_aesni_pclmul,
    vg_aes_gcm_seal_gather_pclmul, vg_aes_gcm_seal_pclmul, vg_aes_gcm_stream_aad_aesni,
    vg_aes_gcm_stream_aad_aesni_pclmul, vg_aes_gcm_stream_aad_pclmul,
    vg_aes_gcm_stream_decrypt_aesni, vg_aes_gcm_stream_decrypt_aesni_pclmul,
    vg_aes_gcm_stream_decrypt_pclmul, vg_aes_gcm_stream_encrypt_aesni,
    vg_aes_gcm_stream_encrypt_aesni_pclmul, vg_aes_gcm_stream_encrypt_pclmul,
    vg_aes_gcm_stream_finish_aesni, vg_aes_gcm_stream_finish_aesni_pclmul,
    vg_aes_gcm_stream_finish_pclmul, vg_aes_gcm_stream_init_aesni,
    vg_aes_gcm_stream_init_aesni_pclmul, vg_aes_gcm_stream_init_pclmul,
    vg_aes_gcm_stream_verify_aesni, vg_aes_gcm_stream_verify_aesni_pclmul,
    vg_aes_gcm_stream_verify_pclmul,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_AESNI_PCLMUL_AVX_FEATURES, vg_aes_gcm_init_aesni_pclmul_avx,
    vg_aes_gcm_open_aesni_pclmul_avx, vg_aes_gcm_seal_aesni_pclmul_avx,
    vg_aes_gcm_stream_aad_aesni_pclmul_avx, vg_aes_gcm_stream_decrypt_aesni_pclmul_avx,
    vg_aes_gcm_stream_encrypt_aesni_pclmul_avx, vg_aes_gcm_stream_finish_aesni_pclmul_avx,
    vg_aes_gcm_stream_init_aesni_pclmul_avx, vg_aes_gcm_stream_verify_aesni_pclmul_avx,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_AESNI_VPCLMUL_FEATURES, VG_AES_GCM_SEAL_VAES_FEATURES,
    VG_AES_GCM_SEAL_VAES_PCLMUL_FEATURES, VG_AES_GCM_SEAL_VAES_VPCLMUL_FEATURES,
    VG_AES_GCM_SEAL_VPCLMUL_FEATURES, vg_aes_gcm_init_aesni_vpclmul, vg_aes_gcm_init_vaes,
    vg_aes_gcm_init_vaes_pclmul, vg_aes_gcm_init_vaes_vpclmul, vg_aes_gcm_init_vpclmul,
    vg_aes_gcm_open_aesni_vpclmul, vg_aes_gcm_open_vaes, vg_aes_gcm_open_vaes_pclmul,
    vg_aes_gcm_open_vaes_vpclmul, vg_aes_gcm_open_vpclmul, vg_aes_gcm_seal_aesni_vpclmul,
    vg_aes_gcm_seal_vaes, vg_aes_gcm_seal_vaes_pclmul, vg_aes_gcm_seal_vaes_vpclmul,
    vg_aes_gcm_seal_vpclmul, vg_aes_gcm_stream_aad_aesni_vpclmul, vg_aes_gcm_stream_aad_vaes,
    vg_aes_gcm_stream_aad_vaes_pclmul, vg_aes_gcm_stream_aad_vaes_vpclmul,
    vg_aes_gcm_stream_aad_vpclmul, vg_aes_gcm_stream_decrypt_aesni_vpclmul,
    vg_aes_gcm_stream_decrypt_vaes, vg_aes_gcm_stream_decrypt_vaes_pclmul,
    vg_aes_gcm_stream_decrypt_vaes_vpclmul, vg_aes_gcm_stream_decrypt_vpclmul,
    vg_aes_gcm_stream_encrypt_aesni_vpclmul, vg_aes_gcm_stream_encrypt_vaes,
    vg_aes_gcm_stream_encrypt_vaes_pclmul, vg_aes_gcm_stream_encrypt_vaes_vpclmul,
    vg_aes_gcm_stream_encrypt_vpclmul, vg_aes_gcm_stream_finish_aesni_vpclmul,
    vg_aes_gcm_stream_finish_vaes, vg_aes_gcm_stream_finish_vaes_pclmul,
    vg_aes_gcm_stream_finish_vaes_vpclmul, vg_aes_gcm_stream_finish_vpclmul,
    vg_aes_gcm_stream_init_aesni_vpclmul, vg_aes_gcm_stream_init_vaes,
    vg_aes_gcm_stream_init_vaes_pclmul, vg_aes_gcm_stream_init_vaes_vpclmul,
    vg_aes_gcm_stream_init_vpclmul, vg_aes_gcm_stream_verify_aesni_vpclmul,
    vg_aes_gcm_stream_verify_vaes, vg_aes_gcm_stream_verify_vaes_pclmul,
    vg_aes_gcm_stream_verify_vaes_vpclmul, vg_aes_gcm_stream_verify_vpclmul,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_VAES_VPCLMUL_AVX512_FEATURES, vg_aes_gcm_init_vaes_vpclmul_avx512,
    vg_aes_gcm_open_vaes_vpclmul_avx512, vg_aes_gcm_seal_vaes_vpclmul_avx512,
    vg_aes_gcm_stream_aad_vaes_vpclmul_avx512, vg_aes_gcm_stream_decrypt_vaes_vpclmul_avx512,
    vg_aes_gcm_stream_encrypt_vaes_vpclmul_avx512, vg_aes_gcm_stream_finish_vaes_vpclmul_avx512,
    vg_aes_gcm_stream_init_vaes_vpclmul_avx512, vg_aes_gcm_stream_verify_vaes_vpclmul_avx512,
};
use crate::arch::gcm::{
    vg_aes_gcm_init, vg_aes_gcm_open, vg_aes_gcm_seal, vg_aes_gcm_stream_aad,
    vg_aes_gcm_stream_decrypt, vg_aes_gcm_stream_encrypt, vg_aes_gcm_stream_finish,
    vg_aes_gcm_stream_init, vg_aes_gcm_stream_verify,
};
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
use crate::arch::gcm::{
    vg_aes_gcm_init_precomputed_vaes_vpclmul_avx512,
    vg_aes_gcm_open_precomputed_vaes_vpclmul_avx512,
    vg_aes_gcm_seal_gather_precomputed_vaes_vpclmul_avx512,
    vg_aes_gcm_seal_precomputed_vaes_vpclmul_avx512,
    vg_aes_gcm_stream_decrypt_precomputed_vaes_vpclmul_avx512,
    vg_aes_gcm_stream_encrypt_precomputed_vaes_vpclmul_avx512,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::gcm::{
    vg_aes_gcm_seal_gather_aesni_pclmul_avx, vg_aes_gcm_seal_gather_aesni_vpclmul,
    vg_aes_gcm_seal_gather_vaes, vg_aes_gcm_seal_gather_vaes_pclmul,
    vg_aes_gcm_seal_gather_vaes_vpclmul, vg_aes_gcm_seal_gather_vaes_vpclmul_avx512,
    vg_aes_gcm_seal_gather_vpclmul,
};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
use alloc::boxed::Box;
use core::mem::MaybeUninit;
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
use core::sync::atomic::{AtomicPtr, AtomicU32, Ordering};

/// A 16-byte block.
type Block = [u8; 16];

/// The largest plaintext (and ciphertext), in bytes: `2^39 − 256` bits
/// (SP 800-38D §5.2.1.1).
const MAX_TEXT: u64 = (1 << 36) - 32;

/// The largest additional data, in bytes: `2^64 − 1` bits, rounded down to
/// whole bytes (SP 800-38D §5.2.1.1).
const MAX_AAD: u64 = (1 << 61) - 1;

/// The implementations of AES and GHASH the functions called call: each
/// combination is an instance of every `vg_aes_gcm_*` function. (A product
/// of `crate::aes::Backend` and a GHASH backend would let a caller pair them
/// any way; one enum of the instances keeps every `match` exhaustive over
/// exactly the functions that exist.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The baseline ISA: `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`.
    Scalar,
    /// AES-NI for AES: the `_aesni` instances.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    AesNi,
    /// PCLMULQDQ for GHASH: the `_pclmul` instances.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    Pclmul,
    /// Both: the `_aesni_pclmul` instances.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    AesNiPclmul,
    /// VAES for AES: the `_vaes` instances.
    #[cfg(target_arch = "x86_64")]
    Vaes,
    /// VPCLMULQDQ for GHASH: the `_vpclmul` instances.
    #[cfg(target_arch = "x86_64")]
    Vpclmul,
    /// VAES and PCLMULQDQ: the `_vaes_pclmul` instances.
    #[cfg(target_arch = "x86_64")]
    VaesPclmul,
    /// AES-NI and VPCLMULQDQ: the `_aesni_vpclmul` instances.
    #[cfg(target_arch = "x86_64")]
    AesNiVpclmul,
    /// VAES and VPCLMULQDQ: the `_vaes_vpclmul` instances.
    #[cfg(target_arch = "x86_64")]
    VaesVpclmul,
    /// VAES and VPCLMULQDQ, with counter mode and GHASH interleaved in
    /// 512-bit registers (AVX512F and AVX512BW): the `_vaes_vpclmul_avx512`
    /// instances.
    #[cfg(target_arch = "x86_64")]
    VaesVpclmulAvx512,
    /// AES-NI and PCLMULQDQ, with counter mode and GHASH interleaved in
    /// 128-bit registers (AVX): the `_aesni_pclmul_avx` instances.
    #[cfg(target_arch = "x86_64")]
    AesNiPclmulAvx,
    /// The AES instructions for AES and PMULL for GHASH (Rust's `aes`
    /// feature stands for both): the `_aes` instances.
    #[cfg(target_arch = "aarch64")]
    Aes,
}

/// The instance of a function for `backend`: the baseline one, then those
/// for x86-64 and x86 (AES-NI, PCLMULQDQ, both), those for x86-64 alone
/// (VAES, VPCLMULQDQ, and their pairs with the others; AES-NI and PCLMULQDQ
/// with AVX) and AArch64 (AES and PMULL).
macro_rules! instance {
    ($backend:expr, $scalar:ident,
     x86_64: [$aesni:ident, $pclmul:ident, $aesni_pclmul:ident],
     vaes: [$vaes:ident, $vpclmul:ident, $vaes_pclmul:ident, $aesni_vpclmul:ident,
        $vaes_vpclmul:ident, $vaes_vpclmul_avx512:ident],
     avx: [$aesni_pclmul_avx:ident],
     aarch64: [$aes:ident]) => {
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
        }
    };
}
// `aes_gcm_siv` (on x86-64, x86, AArch64 and 32-bit ARM so far) chooses its instances with it too.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
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
        (Backend::Aes, Backend::Aes.features()),
        (Backend::Scalar, Backend::Scalar.features()),
    ];

    /// The CPU features its instances need: `seal`'s, which include every
    /// other function's (see the tests).
    const fn features(self) -> Features {
        instance!(self, BASELINE,
            x86_64: [VG_AES_GCM_SEAL_AESNI_FEATURES, VG_AES_GCM_SEAL_PCLMUL_FEATURES,
                VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES],
            vaes: [VG_AES_GCM_SEAL_VAES_FEATURES, VG_AES_GCM_SEAL_VPCLMUL_FEATURES,
                VG_AES_GCM_SEAL_VAES_PCLMUL_FEATURES, VG_AES_GCM_SEAL_AESNI_VPCLMUL_FEATURES,
                VG_AES_GCM_SEAL_VAES_VPCLMUL_FEATURES, VG_AES_GCM_SEAL_VAES_VPCLMUL_AVX512_FEATURES],
            avx: [VG_AES_GCM_SEAL_AESNI_PCLMUL_AVX_FEATURES],
            aarch64: [VG_AES_GCM_SEAL_AES_FEATURES])
    }
}

/// The best implementation a CPU with the features `f` can run.
pub(crate) fn select(f: Features) -> Backend {
    let best = Backend::ALL.iter().find(|(_, need)| f.contains(*need));
    best.map_or(Backend::Scalar, |(b, _)| *b)
}

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
impl Backend {
    /// Whether its instances include the `_precomputed` ones
    /// (`VG.Spec.Gcm.PowersRepr`), whose interleaved loops read the powers
    /// of the hash subkey from the key context instead of computing them on
    /// every call.
    const fn precomputed(self) -> bool {
        match self {
            Backend::VaesVpclmulAvx512 => true,
            Backend::Scalar
            | Backend::AesNi
            | Backend::Pclmul
            | Backend::AesNiPclmul
            | Backend::Vaes
            | Backend::Vpclmul
            | Backend::VaesPclmul
            | Backend::AesNiVpclmul
            | Backend::VaesVpclmul
            | Backend::AesNiPclmulAvx => false,
        }
    }
}

/// The shortest text, in bytes, that reaches the interleaved loops (16
/// blocks at a time), and so gains from the powers of the hash subkey.
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
const POWERS_MIN_LEN: usize = 256;

/// How many calls of at least `POWERS_MIN_LEN` bytes a key makes with the
/// key context of `vg_aes_gcm_init` before it computes the powers of its
/// hash subkey (`Powers::get`): `vg_aes_gcm_init_precomputed` costs about as
/// much as reading the powers saves over this many calls, so a key used for
/// a few messages never pays for them.
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
const POWERS_AFTER: u32 = 32;

/// The key context `vg_aes_gcm_init_precomputed` writes for a key (that of
/// `vg_aes_gcm_init`, then the powers `H¹ … H⁴⁸` of the hash subkey:
/// `VG.Spec.Gcm.PowersRepr`), which the `_precomputed` instances read,
/// computed once the key has been used enough ([`Powers::get`]).
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
struct Powers {
    /// The calls that could have read the powers, before they were ready.
    calls: AtomicU32,
    /// Null, or the key context, from `Box::into_raw`: written before it is
    /// published here (with release ordering), never written again while it
    /// is shared, and freed only by `drop`.
    ctx: AtomicPtr<[u64; 128]>,
}

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
impl Powers {
    /// No powers yet.
    fn new() -> Self {
        Powers {
            calls: AtomicU32::new(0),
            ctx: AtomicPtr::new(core::ptr::null_mut()),
        }
    }

    /// The key context with the powers, for a call (long enough to gain from
    /// them) with `backend`'s instances for `rounds` rounds and the key
    /// context `key` of `vg_aes_gcm_init`: none if `backend` has no
    /// `_precomputed` instances; otherwise the powers, computed by this call
    /// if the key has made `POWERS_AFTER` such calls and they are not ready
    /// yet.
    fn get(&self, backend: Backend, rounds: usize, key: &[u64; 32]) -> Option<&[u64; 128]> {
        if !backend.precomputed() {
            return None;
        }
        let p = self.ctx.load(Ordering::Acquire);
        if !p.is_null() {
            // SAFETY: a published key context (see `ctx`), which the acquire
            // load orders after its writes; it lives as long as `self`.
            return Some(unsafe { &*p });
        }
        if self.calls.fetch_add(1, Ordering::Relaxed) < POWERS_AFTER - 1 {
            return None;
        }
        let mut ctx = Box::new([0; 128]);
        let init = vg_aes_gcm_init_precomputed_vaes_vpclmul_avx512;
        // SAFETY: the key is the first `key_len` bytes (16, 24 or 32, from
        // `rounds`) of its key context `key` (`VG.Spec.Gcm.KeyRepr`: the key
        // schedule, whose first `Nk` words are the key, FIPS 197 §5.2,
        // `VG.Spec.Aes.expandWords`), valid for reads of 256; `ctx` (a new
        // allocation) is valid for reads and writes of 1024. They do not
        // overlap each other or anything on the stack, or wrap around. The
        // CPU has the features of `backend`, the only one with
        // `_precomputed` instances.
        unsafe { init(key.as_ptr().cast(), (rounds - 6) * 4, &mut *ctx) };
        Some(self.publish(ctx))
    }

    /// Publishes `ctx`, unless another thread has published a key context
    /// first: the one published.
    fn publish(&self, ctx: Box<[u64; 128]>) -> &[u64; 128] {
        let p = Box::into_raw(ctx);
        let q = match self.ctx.compare_exchange(
            core::ptr::null_mut(),
            p,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            Ok(_) => p,
            Err(q) => {
                // SAFETY: `p`, from `Box::into_raw`, was not published.
                unsafe { free(p) };
                q
            }
        };
        // SAFETY: as in `get`.
        unsafe { &*q }
    }
}

/// Wipes and frees the key context `p`.
///
/// # Safety
///
/// `p` must come from `Box::into_raw`, and nothing may use it afterwards.
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
unsafe fn free(p: *mut [u64; 128]) {
    // SAFETY: the caller's.
    let mut ctx = unsafe { Box::from_raw(p) };
    zeroize(&mut *ctx);
}

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
impl Clone for Powers {
    /// The same key, with a copy of the powers if they are ready.
    fn clone(&self) -> Self {
        let p = self.ctx.load(Ordering::Acquire);
        let ctx = if p.is_null() {
            p
        } else {
            // SAFETY: as in `get`.
            Box::into_raw(Box::new(unsafe { *p }))
        };
        Powers {
            calls: AtomicU32::new(self.calls.load(Ordering::Relaxed)),
            ctx: AtomicPtr::new(ctx),
        }
    }
}

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
impl Drop for Powers {
    /// Wipes and frees the powers.
    fn drop(&mut self) {
        let p = *self.ctx.get_mut();
        if !p.is_null() {
            // SAFETY: `p` was published (see `ctx`), and `self` is no longer
            // shared.
            unsafe { free(p) };
        }
    }
}

/// Why an AES-GCM operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The key is not 16, 24 or 32 bytes long.
    InvalidKeyLength,
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

/// Fails to compile unless `N` is a tag length §5.2.1.2 allows: 4, 8, 12,
/// 13, 14, 15 or 16 bytes.
macro_rules! assert_tag_length {
    ($n:expr) => {
        const {
            assert!(
                matches!($n, 4 | 8 | 12 | 13 | 14 | 15 | 16),
                "an AES-GCM tag is 4, 8, 12, 13, 14, 15 or 16 bytes long"
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
pub struct AesGcm {
    /// The key context `vg_aes_gcm_init` writes (`VG.Spec.Gcm.KeyRepr`).
    ctx: [u64; 32],
    rounds: usize,
    /// The implementations of AES and GHASH the functions called call.
    backend: Backend,
    /// The key context with the powers of the hash subkey, for the
    /// backends whose loops read them.
    #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
    powers: Powers,
}

impl Drop for AesGcm {
    /// Wipes the key context (`Powers` wipes itself).
    fn drop(&mut self) {
        zeroize(&mut self.ctx);
    }
}

impl AesGcm {
    /// The size of a full tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Prepares `key`, which must be 16, 24 or 32 bytes long (AES-128,
    /// AES-192 or AES-256).
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(Error::InvalidKeyLength);
        }
        let mut k = AesGcm {
            ctx: [0; 32],
            rounds: key.len() / 4 + 6,
            backend: select(detected()),
            #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
            powers: Powers::new(),
        };
        let init = instance!(k.backend, vg_aes_gcm_init,
            x86_64: [vg_aes_gcm_init_aesni, vg_aes_gcm_init_pclmul, vg_aes_gcm_init_aesni_pclmul],
            vaes: [vg_aes_gcm_init_vaes, vg_aes_gcm_init_vpclmul, vg_aes_gcm_init_vaes_pclmul,
                vg_aes_gcm_init_aesni_vpclmul, vg_aes_gcm_init_vaes_vpclmul,
                vg_aes_gcm_init_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_init_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_init_aes]);
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32; `k.ctx` is valid for reads and writes of 256 bytes. They
        // are distinct objects, so they do not overlap each other or anything
        // on the stack, or wrap around the end of the address space. The CPU
        // has the features of the implementation selected.
        unsafe { init(key.as_ptr(), key.len(), &mut k.ctx) };
        Ok(k)
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
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        if data.len() >= POWERS_MIN_LEN
            && let Some(tag) = self.seal_precomputed(nonce, aad, data)
        {
            return Ok(tag);
        }
        let seal = instance!(self.backend, vg_aes_gcm_seal,
            x86_64: [vg_aes_gcm_seal_aesni, vg_aes_gcm_seal_pclmul, vg_aes_gcm_seal_aesni_pclmul],
            vaes: [vg_aes_gcm_seal_vaes, vg_aes_gcm_seal_vpclmul, vg_aes_gcm_seal_vaes_pclmul,
                vg_aes_gcm_seal_aesni_vpclmul, vg_aes_gcm_seal_vaes_vpclmul,
                vg_aes_gcm_seal_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_seal_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_seal_aes]);
        let mut tag: Block = [0; 16];
        // SAFETY: `self.ctx` is the key context `vg_aes_gcm_init` wrote for
        // `self.rounds` (10, 12 or 14) rounds (every implementation writes
        // the same one), valid for reads of 256 bytes; `nonce` and `aad` are
        // valid for reads and `data` for reads and writes of their lengths,
        // and `tag` (a local) for reads and writes of 16 bytes. They are
        // distinct objects (`data` a unique borrow), so the writable ones
        // overlap nothing else, nor anything on the stack, and none wraps
        // around the end of the address space. The CPU has the features of
        // the implementation selected.
        unsafe {
            seal(
                &self.ctx,
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
    /// `N` must be 4, 8, 12, 13, 14, 15 or 16 (SP 800-38D §5.2.1.2); any
    /// other length is an error when the call is compiled. It is a type parameter, fixed
    /// in the caller's code, so that it cannot come from the message: see
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

    /// GCM-AD (§7.2) with `tag`, of a length §5.2.1.2 allows (which the
    /// callers check at compile time; `vg_aes_gcm_open` rejects any other).
    fn open(&self, nonce: &[u8], aad: &[u8], data: &mut [u8], tag: &[u8]) -> Result<(), Error> {
        check_nonce(nonce)?;
        add_len(0, data.len(), MAX_TEXT).map_err(|()| Error::InvalidTextLength)?;
        add_len(0, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        if data.len() >= POWERS_MIN_LEN
            && let Some(r) = self.open_precomputed(nonce, aad, data, tag)
        {
            return r;
        }
        let open = instance!(self.backend, vg_aes_gcm_open,
            x86_64: [vg_aes_gcm_open_aesni, vg_aes_gcm_open_pclmul, vg_aes_gcm_open_aesni_pclmul],
            vaes: [vg_aes_gcm_open_vaes, vg_aes_gcm_open_vpclmul, vg_aes_gcm_open_vaes_pclmul,
                vg_aes_gcm_open_aesni_vpclmul, vg_aes_gcm_open_vaes_vpclmul,
                vg_aes_gcm_open_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_open_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_open_aes]);
        // SAFETY: as in `encrypt_in_place`, with the received tag `tag`
        // valid for reads of its length.
        let ok = unsafe {
            open(
                &self.ctx,
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
        // The descriptors of the pieces, as `vg_aes_gcm_seal_gather` takes
        // them: each its address and its length. Only the first
        // `plaintext.len()` are written, and the function reads only those.
        let mut descs = [const { MaybeUninit::<[usize; 2]>::uninit() }; Self::MAX_PIECES];
        for (d, p) in descs.iter_mut().zip(plaintext) {
            d.write([p.as_ptr() as usize, p.len()]);
        }
        let src: *const [usize; 2] = descs.as_ptr().cast();
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        if out.len() >= POWERS_MIN_LEN
            && let Some(tag) = self.seal_gather_precomputed(nonce, aad, src, plaintext.len(), out)
        {
            return Ok(tag);
        }
        let f = match self.backend {
            Backend::Scalar => vg_aes_gcm_seal_gather,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNi => vg_aes_gcm_seal_gather_aesni,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::Pclmul => vg_aes_gcm_seal_gather_pclmul,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNiPclmul => vg_aes_gcm_seal_gather_aesni_pclmul,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => vg_aes_gcm_seal_gather_vaes,
            #[cfg(target_arch = "x86_64")]
            Backend::Vpclmul => vg_aes_gcm_seal_gather_vpclmul,
            #[cfg(target_arch = "x86_64")]
            Backend::VaesPclmul => vg_aes_gcm_seal_gather_vaes_pclmul,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNiVpclmul => vg_aes_gcm_seal_gather_aesni_vpclmul,
            #[cfg(target_arch = "x86_64")]
            Backend::VaesVpclmul => vg_aes_gcm_seal_gather_vaes_vpclmul,
            #[cfg(target_arch = "x86_64")]
            Backend::VaesVpclmulAvx512 => vg_aes_gcm_seal_gather_vaes_vpclmul_avx512,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNiPclmulAvx => vg_aes_gcm_seal_gather_aesni_pclmul_avx,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => vg_aes_gcm_seal_gather_aes,
        };
        let mut tag: Block = [0; 16];
        // SAFETY: as in `encrypt_in_place`, with `out` valid for reads and
        // writes of `out.len()` bytes; `src` points to `plaintext.len()`
        // initialized descriptors (in `descs`, a local), each the address
        // and the length of a piece valid for reads, which are `out.len()`
        // bytes in all. The pieces and the descriptors are read only, and
        // overlap neither `out` (a unique borrow) nor `tag`, nor anything on
        // the stack the function uses.
        unsafe {
            f(
                &self.ctx,
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

/// The calls of the `_precomputed` instances, out of line so that the
/// shorter calls, which never make them, stay as fast as before.
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
impl AesGcm {
    /// `encrypt_in_place` with the key context with the powers, if
    /// `Powers::get` gives it.
    #[inline(never)]
    fn seal_precomputed(&self, nonce: &[u8], aad: &[u8], data: &mut [u8]) -> Option<Block> {
        let ctx = self.powers.get(self.backend, self.rounds, &self.ctx)?;
        let mut tag: Block = [0; 16];
        let seal = vg_aes_gcm_seal_precomputed_vaes_vpclmul_avx512;
        // SAFETY: as in `encrypt_in_place`, with `ctx` the key context
        // `vg_aes_gcm_init_precomputed` wrote for the same key, valid for
        // reads of 1024 bytes, and the CPU has the features of
        // `self.backend`, whose `_precomputed` instance this is.
        unsafe {
            seal(
                ctx,
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
        Some(tag)
    }

    /// `open` with the key context with the powers, if `Powers::get` gives
    /// it.
    #[inline(never)]
    fn open_precomputed(
        &self,
        nonce: &[u8],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8],
    ) -> Option<Result<(), Error>> {
        let ctx = self.powers.get(self.backend, self.rounds, &self.ctx)?;
        let open = vg_aes_gcm_open_precomputed_vaes_vpclmul_avx512;
        // SAFETY: as in `seal_precomputed`, with the received tag `tag`
        // valid for reads of its length.
        let ok = unsafe {
            open(
                ctx,
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
        // As in `open`.
        Some(if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        })
    }

    /// `encrypt`'s call with the key context with the powers, if
    /// `Powers::get` gives it.
    #[inline(never)]
    fn seal_gather_precomputed(
        &self,
        nonce: &[u8],
        aad: &[u8],
        src: *const [usize; 2],
        count: usize,
        out: &mut [u8],
    ) -> Option<Block> {
        let ctx = self.powers.get(self.backend, self.rounds, &self.ctx)?;
        let mut tag: Block = [0; 16];
        // SAFETY: as in `encrypt`, with `src` the `count` descriptors it
        // wrote, and with `ctx` the key context with the powers, as in
        // `seal_precomputed`.
        unsafe {
            vg_aes_gcm_seal_gather_precomputed_vaes_vpclmul_avx512(
                ctx,
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                src,
                count,
                out.as_mut_ptr(),
                out.len(),
                &mut tag,
            )
        };
        Some(tag)
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
        let init = instance!(key.backend, vg_aes_gcm_stream_init,
            x86_64: [vg_aes_gcm_stream_init_aesni, vg_aes_gcm_stream_init_pclmul,
                vg_aes_gcm_stream_init_aesni_pclmul],
            vaes: [vg_aes_gcm_stream_init_vaes, vg_aes_gcm_stream_init_vpclmul,
                vg_aes_gcm_stream_init_vaes_pclmul, vg_aes_gcm_stream_init_aesni_vpclmul,
                vg_aes_gcm_stream_init_vaes_vpclmul,
                vg_aes_gcm_stream_init_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_stream_init_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_stream_init_aes]);
        // SAFETY: `key.ctx` is a key context (as in
        // `AesGcm::encrypt_in_place`), valid for reads of 256 bytes, `nonce`
        // for reads of `nonce.len()`, and `s.state` for reads and writes of
        // 80. They are distinct objects, so the writable one overlaps nothing
        // else, nor anything on the stack, and none wraps around. The CPU has
        // the features of the implementation selected.
        unsafe { init(&key.ctx, nonce.as_ptr(), nonce.len(), &mut s.state) };
        Ok(s)
    }

    /// Absorbs more additional data, which must all come before the text.
    fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        if self.in_text {
            return Err(Error::AadAfterText);
        }
        let aad_len =
            add_len(self.aad_len, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        let f = instance!(self.key.backend, vg_aes_gcm_stream_aad,
            x86_64: [vg_aes_gcm_stream_aad_aesni, vg_aes_gcm_stream_aad_pclmul,
                vg_aes_gcm_stream_aad_aesni_pclmul],
            vaes: [vg_aes_gcm_stream_aad_vaes, vg_aes_gcm_stream_aad_vpclmul,
                vg_aes_gcm_stream_aad_vaes_pclmul, vg_aes_gcm_stream_aad_aesni_vpclmul,
                vg_aes_gcm_stream_aad_vaes_vpclmul,
                vg_aes_gcm_stream_aad_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_stream_aad_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_stream_aad_aes]);
        // SAFETY: as in `new`; `self.state` represents a message with
        // `self.aad_len` bytes of additional data and no text yet.
        unsafe {
            f(
                &self.key.ctx,
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
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        if data.len() >= POWERS_MIN_LEN && self.update_precomputed(data) {
            self.text_len = text_len;
            return Ok(());
        }
        let f = if DECRYPT {
            instance!(self.key.backend, vg_aes_gcm_stream_decrypt,
                x86_64: [vg_aes_gcm_stream_decrypt_aesni, vg_aes_gcm_stream_decrypt_pclmul,
                    vg_aes_gcm_stream_decrypt_aesni_pclmul],
                vaes: [vg_aes_gcm_stream_decrypt_vaes, vg_aes_gcm_stream_decrypt_vpclmul,
                    vg_aes_gcm_stream_decrypt_vaes_pclmul, vg_aes_gcm_stream_decrypt_aesni_vpclmul,
                    vg_aes_gcm_stream_decrypt_vaes_vpclmul,
                vg_aes_gcm_stream_decrypt_vaes_vpclmul_avx512],
                avx: [vg_aes_gcm_stream_decrypt_aesni_pclmul_avx],
                aarch64: [vg_aes_gcm_stream_decrypt_aes])
        } else {
            instance!(self.key.backend, vg_aes_gcm_stream_encrypt,
                x86_64: [vg_aes_gcm_stream_encrypt_aesni, vg_aes_gcm_stream_encrypt_pclmul,
                    vg_aes_gcm_stream_encrypt_aesni_pclmul],
                vaes: [vg_aes_gcm_stream_encrypt_vaes, vg_aes_gcm_stream_encrypt_vpclmul,
                    vg_aes_gcm_stream_encrypt_vaes_pclmul, vg_aes_gcm_stream_encrypt_aesni_vpclmul,
                    vg_aes_gcm_stream_encrypt_vaes_vpclmul,
                vg_aes_gcm_stream_encrypt_vaes_vpclmul_avx512],
                avx: [vg_aes_gcm_stream_encrypt_aesni_pclmul_avx],
                aarch64: [vg_aes_gcm_stream_encrypt_aes])
        };
        // SAFETY: as in `new`, with `data` valid for reads and writes of
        // `data.len()` bytes (a unique borrow, so it overlaps nothing else);
        // `self.state` represents a message with `self.aad_len` bytes of
        // additional data and `self.text_len` of text.
        unsafe {
            f(
                &self.key.ctx,
                self.key.rounds,
                &mut self.state,
                self.aad_len,
                self.text_len,
                data.as_mut_ptr(),
                data.len(),
            )
        };
        self.text_len = text_len;
        Ok(())
    }
}

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
impl<const DECRYPT: bool> Stream<'_, DECRYPT> {
    /// `update` with the key context with the powers, if `Powers::get`
    /// gives it: whether it did (leaving `self.text_len` to the caller).
    #[inline(never)]
    fn update_precomputed(&mut self, data: &mut [u8]) -> bool {
        let Some(ctx) = self
            .key
            .powers
            .get(self.key.backend, self.key.rounds, &self.key.ctx)
        else {
            return false;
        };
        let f = if DECRYPT {
            vg_aes_gcm_stream_decrypt_precomputed_vaes_vpclmul_avx512
        } else {
            vg_aes_gcm_stream_encrypt_precomputed_vaes_vpclmul_avx512
        };
        // SAFETY: as in `update`, with `ctx` the key context
        // `vg_aes_gcm_init_precomputed` wrote for the same key, valid for
        // reads of 1024 bytes (the other streaming functions read the key
        // context of `vg_aes_gcm_init` for it, whose hash subkey and key
        // schedule are the same: `VG.Spec.Gcm.StreamRepr` depends on those
        // alone), and the CPU has the features of `self.key.backend`, whose
        // `_precomputed` instances these are.
        unsafe {
            f(
                ctx,
                self.key.rounds,
                &mut self.state,
                self.aad_len,
                self.text_len,
                data.as_mut_ptr(),
                data.len(),
            )
        };
        true
    }
}

impl Stream<'_, false> {
    /// Finishes the message and returns its 16-byte tag.
    fn finish(mut self) -> Block {
        let f = instance!(self.key.backend, vg_aes_gcm_stream_finish,
            x86_64: [vg_aes_gcm_stream_finish_aesni, vg_aes_gcm_stream_finish_pclmul,
                vg_aes_gcm_stream_finish_aesni_pclmul],
            vaes: [vg_aes_gcm_stream_finish_vaes, vg_aes_gcm_stream_finish_vpclmul,
                vg_aes_gcm_stream_finish_vaes_pclmul, vg_aes_gcm_stream_finish_aesni_vpclmul,
                vg_aes_gcm_stream_finish_vaes_vpclmul,
                vg_aes_gcm_stream_finish_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_stream_finish_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_stream_finish_aes]);
        let mut tag: Block = [0; 16];
        // SAFETY: as in `update`, with `tag` (a local) valid for reads and
        // writes of 16 bytes. `update_aad` and `update` checked the lengths
        // (§5.2.1.1).
        unsafe {
            f(
                &self.key.ctx,
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
    /// Finishes the message and checks that `tag` (of a length §5.2.1.2
    /// allows, which the callers check at compile time;
    /// `vg_aes_gcm_stream_verify` rejects any other) is the first
    /// `tag.len()` bytes of its tag.
    fn verify(mut self, tag: &[u8]) -> Result<(), Error> {
        let f = instance!(self.key.backend, vg_aes_gcm_stream_verify,
            x86_64: [vg_aes_gcm_stream_verify_aesni, vg_aes_gcm_stream_verify_pclmul,
                vg_aes_gcm_stream_verify_aesni_pclmul],
            vaes: [vg_aes_gcm_stream_verify_vaes, vg_aes_gcm_stream_verify_vpclmul,
                vg_aes_gcm_stream_verify_vaes_pclmul, vg_aes_gcm_stream_verify_aesni_vpclmul,
                vg_aes_gcm_stream_verify_vaes_vpclmul,
                vg_aes_gcm_stream_verify_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_stream_verify_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_stream_verify_aes]);
        // SAFETY: as in `finish`, with the received tag `tag` valid for
        // reads of its length.
        let ok = unsafe {
            f(
                &self.key.ctx,
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
    /// `N` must be 4, 8, 12, 13, 14, 15 or 16 (SP 800-38D §5.2.1.2); any
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
    use super::{AesGcm, Backend, Error, MAX_AAD, MAX_TEXT, add_len, select};
    use crate::cpu::{Features, detected};

    /// The implementation chosen for each set of features: AES's and
    /// GHASH's, independently.
    #[test]
    fn backend() {
        let f = |names: &[&str]| select(Features::of(names));
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            assert_eq!(f(&["aes", "pclmulqdq", "ssse3"]), Backend::AesNiPclmul);
            assert_eq!(f(&["aes", "ssse3"]), Backend::AesNi);
            assert_eq!(f(&["pclmulqdq", "ssse3"]), Backend::Pclmul);
        }
        // AES-NI needs SSSE3 too on x86-64 (`vg_aes_ctr32_aesni`'s byte
        // shuffles), not on x86.
        #[cfg(target_arch = "x86_64")]
        assert_eq!(f(&["aes", "pclmulqdq"]), Backend::Scalar);
        // VAES and VPCLMULQDQ, each with the other, the other's 128-bit
        // instruction or neither; their 256-bit code needs AVX2 too.
        #[cfg(target_arch = "x86_64")]
        {
            let all = [
                "aes",
                "avx",
                "avx2",
                "pclmulqdq",
                "ssse3",
                "vaes",
                "vpclmulqdq",
            ];
            assert_eq!(f(&all), Backend::VaesVpclmul);
            // The 512-bit loops need AVX512F and AVX512BW too.
            let avx512 = [&all[..], &["avx512f", "avx512bw"]].concat();
            assert_eq!(f(&avx512), Backend::VaesVpclmulAvx512);
            assert_eq!(f(&[&all[..], &["avx512f"]].concat()), Backend::VaesVpclmul);
            assert_eq!(f(&all[..6]), Backend::VaesPclmul);
            assert_eq!(
                f(&["aes", "avx", "avx2", "pclmulqdq", "ssse3", "vpclmulqdq"]),
                Backend::AesNiVpclmul
            );
            assert_eq!(f(&["aes", "avx", "avx2", "ssse3", "vaes"]), Backend::Vaes);
            assert_eq!(
                f(&["avx", "avx2", "pclmulqdq", "ssse3", "vpclmulqdq"]),
                Backend::Vpclmul
            );
            // AES-NI and PCLMULQDQ with AVX (and without AVX2, which the
            // 256-bit code needs): one pass.
            assert_eq!(
                f(&["aes", "avx", "pclmulqdq", "ssse3", "vaes", "vpclmulqdq"]),
                Backend::AesNiPclmulAvx
            );
            assert_eq!(
                f(&["aes", "avx", "pclmulqdq", "ssse3"]),
                Backend::AesNiPclmulAvx
            );
            assert_eq!(f(&["aes", "avx", "ssse3"]), Backend::AesNi);
        }
        #[cfg(target_arch = "x86")]
        {
            assert_eq!(f(&["aes"]), Backend::AesNi);
            assert_eq!(f(&["aes", "pclmulqdq"]), Backend::AesNi);
        }
        #[cfg(target_arch = "aarch64")]
        assert_eq!(f(&["aes"]), Backend::Aes);
        assert_eq!(f(&[]), Backend::Scalar);
        let best = AesGcm::new(&[0; 16]).unwrap().backend;
        assert_eq!(best, select(detected()));
        for &(b, need) in Backend::ALL {
            assert_eq!(need, b.features());
        }
    }

    /// Every function's instances need at most the features `seal`'s do,
    /// which `select` checks (`init` needs only AES's, `stream_init` and
    /// `stream_aad` only GHASH's).
    #[test]
    fn features() {
        #[cfg(target_arch = "x86")]
        {
            use crate::arch::gcm::*;
            let groups: [(Features, &[Features]); 3] = [
                (
                    VG_AES_GCM_SEAL_AESNI_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AESNI_FEATURES,
                        VG_AES_GCM_OPEN_AESNI_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_AESNI_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_PCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_STREAM_AAD_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_PCLMUL_FEATURES,
                        VG_AES_GCM_OPEN_PCLMUL_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_PCLMUL_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_OPEN_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_AESNI_PCLMUL_FEATURES,
                    ][..],
                ),
            ];
            for (seal, others) in groups {
                for other in others {
                    assert!(seal.contains(*other));
                }
            }
        }
        #[cfg(target_arch = "x86_64")]
        {
            use crate::arch::gcm::*;
            let groups: [(Features, &[Features]); 3] = [
                (
                    VG_AES_GCM_SEAL_AESNI_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AESNI_FEATURES,
                        VG_AES_GCM_OPEN_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AESNI_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AESNI_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AESNI_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_PCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_OPEN_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_PCLMUL_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_PCLMUL_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_AESNI_PCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_OPEN_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AESNI_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AESNI_PCLMUL_FEATURES,
                    ][..],
                ),
            ];
            for (seal, others) in groups {
                for other in others {
                    assert!(seal.contains(*other));
                }
            }
            let groups: [(Features, &[Features]); 7] = [
                (
                    VG_AES_GCM_SEAL_AESNI_PCLMUL_AVX_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_OPEN_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_STREAM_INIT_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_STREAM_AAD_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AESNI_PCLMUL_AVX_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_VAES_FEATURES,
                    &[
                        VG_AES_GCM_INIT_VAES_FEATURES,
                        VG_AES_GCM_OPEN_VAES_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_VAES_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_VAES_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_VAES_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_VAES_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_VAES_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_VPCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_OPEN_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_VPCLMUL_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_VPCLMUL_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_VAES_PCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_INIT_VAES_PCLMUL_FEATURES,
                        VG_AES_GCM_OPEN_VAES_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_VAES_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_VAES_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_VAES_PCLMUL_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_VAES_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_VAES_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_VAES_PCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_VAES_PCLMUL_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_AESNI_VPCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_INIT_AESNI_VPCLMUL_FEATURES,
                        VG_AES_GCM_OPEN_AESNI_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_AESNI_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_AESNI_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_AESNI_VPCLMUL_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_AESNI_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_AESNI_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_AESNI_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_AESNI_VPCLMUL_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_VAES_VPCLMUL_FEATURES,
                    &[
                        VG_AES_GCM_INIT_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_OPEN_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_INIT_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_AAD_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_VAES_VPCLMUL_FEATURES,
                    ][..],
                ),
                (
                    VG_AES_GCM_SEAL_VAES_VPCLMUL_AVX512_FEATURES,
                    &[
                        VG_AES_GCM_INIT_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_OPEN_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_STREAM_INIT_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_STREAM_AAD_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_STREAM_FINISH_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_STREAM_VERIFY_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_INIT_PRECOMPUTED_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_SEAL_PRECOMPUTED_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_OPEN_PRECOMPUTED_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_PRECOMPUTED_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_PRECOMPUTED_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_PRECOMPUTED_VAES_VPCLMUL_AVX512_FEATURES,
                    ][..],
                ),
            ];
            for (seal, others) in groups {
                for other in others {
                    assert!(seal.contains(*other));
                }
            }
        }
        #[cfg(target_arch = "aarch64")]
        {
            use crate::arch::gcm::*;
            for other in [
                VG_AES_GCM_INIT_AES_FEATURES,
                VG_AES_GCM_OPEN_AES_FEATURES,
                VG_AES_GCM_STREAM_INIT_AES_FEATURES,
                VG_AES_GCM_STREAM_AAD_AES_FEATURES,
                VG_AES_GCM_STREAM_ENCRYPT_AES_FEATURES,
                VG_AES_GCM_STREAM_DECRYPT_AES_FEATURES,
                VG_AES_GCM_STREAM_FINISH_AES_FEATURES,
                VG_AES_GCM_STREAM_VERIFY_AES_FEATURES,
                VG_AES_GCM_SEAL_GATHER_AES_FEATURES,
            ] {
                assert!(VG_AES_GCM_SEAL_AES_FEATURES.contains(other));
            }
        }
    }

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

    /// One-shot encryption and decryption of whole blocks in one pass (from
    /// 16 blocks, interleaved on CPUs with VAES and VPCLMULQDQ) agree with
    /// the streaming functions, and a wrong tag leaves the ciphertext as it
    /// was.
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

    impl AesGcm {
        /// The same key, with `backend`'s instances.
        fn with_backend(&self, backend: Backend) -> AesGcm {
            let mut k = self.clone();
            k.backend = backend;
            k
        }
    }

    /// Every implementation the CPU can run encrypts and decrypts long
    /// messages (whole groups of 16 blocks, which some implementations
    /// interleave, and the blocks left) as the baseline one does, one-shot
    /// and streaming.
    #[test]
    fn backends_agree() {
        let msg: [u8; 1300] = core::array::from_fn(|i| (i * 13 + 1) as u8);
        let aad = [9u8; 7];
        let nonce = [2u8; 12];
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&[0x5a; 32][..key_len]).unwrap();
            let base = k.with_backend(Backend::Scalar);
            for &(b, need) in Backend::ALL {
                if !detected().contains(need) {
                    continue;
                }
                let k = k.with_backend(b);
                for len in [256, 300, 512, 1024, 1300] {
                    let mut want = msg;
                    let want_tag = base
                        .encrypt_in_place(&nonce, &aad, &mut want[..len])
                        .unwrap();
                    let mut ct = msg;
                    let tag = k.encrypt_in_place(&nonce, &aad, &mut ct[..len]).unwrap();
                    assert_eq!((&ct[..len], tag), (&want[..len], want_tag), "{b:?}");
                    let mut e = k.encryptor(&nonce).unwrap();
                    e.update_aad(&aad).unwrap();
                    let mut s = msg;
                    e.update(&mut s[..len]).unwrap();
                    assert_eq!((&s[..len], e.finalize()), (&want[..len], want_tag), "{b:?}");
                    k.decrypt_in_place(&nonce, &aad, &mut ct[..len], &tag)
                        .unwrap();
                    assert_eq!(&ct[..len], &msg[..len], "{b:?}");
                    let (a, c) = msg[..len].split_at(len / 3);
                    for pieces in [&[&msg[..len]][..], &[a, c]] {
                        let mut out = [0u8; 1300];
                        let tag = k.encrypt(&nonce, &aad, pieces, &mut out[..len]);
                        assert_eq!((&out[..len], tag), (&want[..len], Ok(want_tag)), "{b:?}");
                    }
                }
            }
        }
    }

    /// A key whose backend has `_precomputed` instances computes the powers
    /// of its hash subkey after `POWERS_AFTER` calls long enough to use
    /// them, and then encrypts and decrypts, one-shot and streaming, as the
    /// baseline does; shorter calls never count, and a key whose backend has
    /// no such instances never computes them. Of two threads computing them
    /// at once, the second to publish them uses the first's.
    #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
    #[test]
    fn powers() {
        use super::{POWERS_AFTER, POWERS_MIN_LEN};
        use alloc::boxed::Box;
        use core::sync::atomic::Ordering;
        let msg: [u8; 700] = core::array::from_fn(|i| (i * 11 + 5) as u8);
        let aad = [3u8; 5];
        let nonce = [7u8; 12];
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&[0x3c; 32][..key_len]).unwrap();
            let base = k.with_backend(Backend::Scalar);
            assert!(
                base.powers
                    .get(base.backend, base.rounds, &base.ctx)
                    .is_none()
            );
            // Without the backend's features, only what needs none of them.
            if !detected().contains(Backend::VaesVpclmulAvx512.features()) {
                continue;
            }
            let k = k.with_backend(Backend::VaesVpclmulAvx512);
            let ready = |k: &AesGcm| !k.powers.ctx.load(Ordering::Acquire).is_null();
            // Short calls neither use nor count toward the powers.
            let mut short = msg;
            let tag = k
                .encrypt_in_place(&nonce, &aad, &mut short[..POWERS_MIN_LEN - 1])
                .unwrap();
            k.decrypt_in_place(&nonce, &aad, &mut short[..POWERS_MIN_LEN - 1], &tag)
                .unwrap();
            let mut e = k.encryptor(&nonce).unwrap();
            e.update(&mut short[..POWERS_MIN_LEN - 1]).unwrap();
            assert_eq!(k.powers.calls.load(Ordering::Relaxed), 0);
            let fresh = k.clone();
            // Each round makes five calls: `encrypt_in_place`, two
            // streaming updates and two `decrypt_in_place`.
            for i in 0..POWERS_AFTER / 5 + 2 {
                assert_eq!(ready(&k), 5 * i >= POWERS_AFTER);
                let len = [256, 300, 512, 700][i as usize % 4];
                let mut want = msg;
                let want_tag = base
                    .encrypt_in_place(&nonce, &aad, &mut want[..len])
                    .unwrap();
                let mut ct = msg;
                let tag = k.encrypt_in_place(&nonce, &aad, &mut ct[..len]).unwrap();
                assert_eq!((&ct[..len], tag), (&want[..len], want_tag));
                let mut e = k.encryptor(&nonce).unwrap();
                e.update_aad(&aad).unwrap();
                let mut st = msg;
                e.update(&mut st[..len]).unwrap();
                assert_eq!((&st[..len], e.finalize()), (&want[..len], want_tag));
                let mut d = k.decryptor(&nonce).unwrap();
                d.update_aad(&aad).unwrap();
                d.update(&mut st[..len]).unwrap();
                d.finalize(&tag).unwrap();
                assert_eq!(&st[..len], &msg[..len]);
                let mut bad = tag;
                bad[0] ^= 1;
                let rejected = k.decrypt_in_place(&nonce, &aad, &mut ct[..len], &bad);
                assert_eq!(rejected, Err(Error::TagMismatch));
                k.decrypt_in_place(&nonce, &aad, &mut ct[..len], &tag)
                    .unwrap();
                assert_eq!(&ct[..len], &msg[..len]);
            }
            // Out of place, with the powers.
            let mut want = msg;
            let want_tag = base.encrypt_in_place(&nonce, &aad, &mut want).unwrap();
            let mut out = [0u8; 700];
            let tag = k.encrypt(&nonce, &aad, &[&msg[..1], &msg[1..]], &mut out);
            assert_eq!((out, tag), (want, Ok(want_tag)));
            // A clone copies the powers if they are ready, and not otherwise.
            let copy = k.clone();
            let powers = k.powers.get(k.backend, k.rounds, &k.ctx).unwrap();
            let copied = copy.powers.get(copy.backend, copy.rounds, &copy.ctx);
            assert_eq!(copied, Some(powers));
            assert!(!core::ptr::eq(copied.unwrap(), powers));
            assert!(!ready(&fresh.clone()));
            // A key context published second is dropped for the first.
            let first = fresh.powers.publish(Box::new(*powers));
            let second = fresh.powers.publish(Box::new([0; 128]));
            assert!(core::ptr::eq(first, second));
            assert_eq!(second, powers);
        }
    }

    /// Streaming a long message in three updates, split on and off block
    /// boundaries (each update finishes the block the text so far left
    /// partial, then takes its whole blocks in one pass), agrees with the
    /// one-shot functions, in both directions.
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

    /// Every tag length §5.2.1.2 allows.
    #[test]
    fn truncated_tags() {
        truncated::<4>();
        truncated::<8>();
        truncated::<12>();
        truncated::<13>();
        truncated::<14>();
        truncated::<15>();
        truncated::<16>();
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
        assert_eq!(
            k.encrypt(&[], &[], &[&msg[..4]], &mut out),
            Err(Error::InvalidNonceLength)
        );
    }

    #[test]
    fn errors() {
        assert_eq!(AesGcm::new(&[0; 15]).err(), Some(Error::InvalidKeyLength));
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
