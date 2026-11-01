//! AES-GCM (NIST SP 800-38D) with 128-, 192- and 256-bit AES keys.
//!
//! Key setup, in-place AEAD and the streaming operations are verified assembly: `vg_aes_gcm_init` (contract
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
//! into one output buffer. Usually this is one call of `vg_aes_gcm_seal_gather`
//! (`VG.Spec.Gcm.sealGatherContract`), which reads each piece where it is;
//! with a prepared key, of `vg_aes_gcm_seal_gather_prepared`, which seals a
//! TLS record (a 96-bit nonce, at most 16 bytes of AAD, and a piece and
//! what ends at most 16 bytes after its whole blocks) from its first piece
//! by `vg_aes_gcm_seal_split_prepared`
//! (`VG.Spec.Gcm.sealSplitPreparedContract`). On 256-bit registers, a
//! record of a multiple of 16 blocks from 2048 bytes on, whose last block
//! the first piece starts and the second fills, is one call of
//! `vg_aes_gcm_seal_split_prepared` for the first piece up to its last
//! whole group of 16 blocks, the rest of it and the second piece copied to
//! the end of the output first.
//!
//! # Tags
//!
//! Encryption returns the full 16-byte tag; a protocol that sends a shorter
//! one sends its first bytes. Decryption takes a `&[u8; 16]`
//! ([`AesGcm::decrypt_in_place`], [`AesGcmDecryptor::finalize`]), or, for a
//! protocol that truncates the tag, a `&[u8; N]` whose length `N` is a type
//! parameter ([`AesGcm::decrypt_in_place_truncated`],
//! [`AesGcmDecryptor::finalize_truncated`]): 4 through 16 bytes, checked
//! at compile time. Lengths 5–7 and 9–11 are extensions to SP 800-38D
//! §5.2.1.2; the standard allows only 4, 8, 12, 13, 14, 15 and 16 bytes.
//! The length is never taken from a slice, because a slice's length
//! often comes from the message: a protocol that splits a message with
//! `msg.split_at(msg.len().saturating_sub(16))` would, given a 4-byte
//! message, check an empty ciphertext against a 4-byte tag, which an
//! attacker forges with probability 2⁻³² instead of 2⁻¹²⁸. Tags of 4 and 8
//! bytes are only for the applications of SP 800-38D Appendix C, which
//! bounds the lengths of the messages and the number of decryptions under
//! one key. These application-level restrictions are the caller's responsibility.
//! Shorter tags provide less protection against forgery.
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
//! On x86-64, the `_vaes_vpclmul_avx512` instances also have `_prepared`
//! ones (`VG.Spec.Gcm.PreparedPowersRepr`), whose interleaved loops read
//! encoded pairs of powers `H¹ … H⁴⁸` from a larger key context, which
//! `vg_aes_gcm_prepare` writes from the key context of `vg_aes_gcm_init`,
//! instead of computing them on every call; the `_vaes_vpclmul` and
//! `_aesni_pclmul_avx` instances have `_prepared16` ones
//! (`VG.Spec.Gcm.PreparedPowers16Repr`), which read only `H¹ … H¹⁶` (`H¹ …
//! H¹⁵` on 128-bit registers), the first 512 bytes of the same context, which
//! `vg_aes_gcm_prepare16` writes in a third of the time or less. The `_vaes_vpclmul_avx512` loops also
//! load the AES round keys into `zmm16`–`zmm31` once per block call and
//! reuse them across batches. `AesGcm::new` computes the prepared context,
//! and every message and streaming update uses it, whatever its length: each
//! `_prepared` instance chooses its path for every length itself (the
//! `_vaes_vpclmul_avx512` short path copies its powers from the context; the
//! others have a path for TLS records, a 12-byte nonce and at most 16 bytes
//! of additional data, or loops that take two blocks or more).
//!
//! On PPC64LE, `encrypt` uses `vg_aes_gcm_seal_split` for messages of at
//! least 512 bytes. Complete blocks of the first nonempty piece are read
//! directly; its partial block and the remaining pieces are copied into
//! the output suffix before the shared fused encryption and GHASH pass.
//!
//! On AArch64, the `_aes` instances of `seal` and `open` have
//! `_with_powers` ones (`VG.Spec.Gcm.Powers8Repr`), whose one call of
//! `vg_ghash_with_powers_aes` loads `H¹` to `H⁸` from a 128-byte buffer of
//! the key's own, next to the key context of `vg_aes_gcm_init`, instead of
//! computing them, which `AesGcm::new` fills with `vg_ghash_store_powers_aes`.
//! Every message uses them (which hash a message of one block or less
//! with `vg_ghash_aes`, needing no powers):
//! `vg_ghash_with_powers_aes` loads `H · x⁻¹` rather than computing it, and
//! `encrypt` copies its pieces to its output with `memcpy` and seals them
//! there, rather than taking `vg_aes_gcm_seal_gather`'s 16-byte steps and
//! single bytes. Streaming keeps the plain functions.
//!
//! On either, which instance a call takes depends only on public values: the
//! lengths of its text (and, for `encrypt`, of its pieces, nonce and
//! additional data), never on the key, the text or the tags.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::gcm::vg_aes_gcm_seal_gather;
#[cfg(all(target_arch = "powerpc64", target_endian = "little"))]
use crate::arch::gcm::vg_aes_gcm_seal_split;
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
use crate::arch::gcm::{
    VG_AES_GCM_PREPARE_VPCLMUL_AVX512_FEATURES, VG_AES_GCM_PREPARE16_PCLMUL_AVX_CTX_WRITTEN,
    VG_AES_GCM_PREPARE16_PCLMUL_AVX_FEATURES, VG_AES_GCM_PREPARE16_VPCLMUL_CTX_WRITTEN,
    VG_AES_GCM_PREPARE16_VPCLMUL_FEATURES, vg_aes_gcm_open_prepared_vaes_vpclmul_avx512,
    vg_aes_gcm_open_prepared16_aesni_pclmul_avx, vg_aes_gcm_open_prepared16_vaes_vpclmul,
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
#[cfg(target_arch = "aarch64")]
use crate::arch::gcm::{
    VG_AES_GCM_SEAL_WITH_POWERS_AES_SHA3_FEATURES, vg_aes_gcm_init_aes_sha3,
    vg_aes_gcm_open_aes_sha3, vg_aes_gcm_seal_aes_sha3, vg_aes_gcm_seal_gather_aes_sha3,
    vg_aes_gcm_stream_aad_aes_sha3, vg_aes_gcm_stream_decrypt_aes_sha3,
    vg_aes_gcm_stream_encrypt_aes_sha3, vg_aes_gcm_stream_finish_aes_sha3,
    vg_aes_gcm_stream_init_aes_sha3, vg_aes_gcm_stream_verify_aes_sha3,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::gcm::{
    VG_GHASH_STORE_POWERS_AES_SCRATCH_WRITTEN, vg_aes_gcm_open_with_powers_aes,
    vg_aes_gcm_seal_with_powers_aes, vg_ghash_store_powers_aes,
};
use crate::arch::gcm::{
    vg_aes_gcm_init, vg_aes_gcm_open, vg_aes_gcm_seal, vg_aes_gcm_stream_aad,
    vg_aes_gcm_stream_decrypt, vg_aes_gcm_stream_encrypt, vg_aes_gcm_stream_finish,
    vg_aes_gcm_stream_init, vg_aes_gcm_stream_verify,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::gcm::{
    vg_aes_gcm_open_with_powers_aes_sha3, vg_aes_gcm_seal_with_powers_aes_sha3,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::gcm::{
    vg_aes_gcm_seal_gather_aesni_pclmul_avx, vg_aes_gcm_seal_gather_aesni_vpclmul,
    vg_aes_gcm_seal_gather_vaes, vg_aes_gcm_seal_gather_vaes_pclmul,
    vg_aes_gcm_seal_gather_vaes_vpclmul, vg_aes_gcm_seal_gather_vaes_vpclmul_avx512,
    vg_aes_gcm_seal_gather_vpclmul,
};
use crate::cpu::detected;
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
    /// Both, with FEAT_SHA3's `eor3`: the `_aes_sha3` instances, whose
    /// `_with_powers` and `_store_powers` functions interleave counter mode
    /// and GHASH eight blocks at a time on the records of TLS (the others
    /// are the `_aes` code).
    #[cfg(target_arch = "aarch64")]
    AesSha3,
}

/// The instance of a function for `backend`: the baseline one, then those
/// for x86-64 and x86 (AES-NI, PCLMULQDQ, both), those for x86-64 alone
/// (VAES, VPCLMULQDQ, and their pairs with the others; AES-NI and PCLMULQDQ
/// with AVX) and AArch64 (AES and PMULL, without and with FEAT_SHA3).
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
    all(target_arch = "powerpc64", target_endian = "little")
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

    /// The CPU features its instances need: `seal`'s, which include every
    /// other function's (see the tests); for `AesSha3`, whose `seal` is
    /// `Aes`'s, `seal_with_powers`'s.
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

/// The type of an emitted function with arguments `$a` (and result `$r`),
/// in the ABI the target's functions are emitted in.
#[cfg(target_arch = "x86_64")]
macro_rules! asm_fn {
    ($($a:ty),* $(=> $r:ty)?) => { unsafe extern "sysv64" fn($($a),*) $(-> $r)? };
}
#[cfg(not(target_arch = "x86_64"))]
macro_rules! asm_fn {
    ($($a:ty),* $(=> $r:ty)?) => { unsafe extern "C" fn($($a),*) $(-> $r)? };
}

/// `vg_aes_gcm_init`.
type InitFn = asm_fn!(*const u8, usize, *mut [u64; 32]);
/// `vg_aes_gcm_seal`, on the key's context (`KeyCtx`).
type SealFn = asm_fn!(
    *const KeyCtx,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *mut u8,
    usize,
    *mut [u8; 16]
);
/// `vg_aes_gcm_open`, on the key's context.
type OpenFn = asm_fn!(*const KeyCtx, usize, *const u8, usize, *const u8, usize, *mut u8, usize, *const u8,
    usize => u32);
/// `vg_aes_gcm_seal_gather`, on the key's context.
type SealGatherFn = asm_fn!(
    *const KeyCtx,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const [usize; 2],
    usize,
    *mut u8,
    usize,
    *mut [u8; 16]
);
/// `vg_aes_gcm_stream_init`.
type StreamInitFn = asm_fn!(*const [u64; 32], *const u8, usize, *mut [u64; 10]);
/// `vg_aes_gcm_stream_aad`.
type StreamAadFn = asm_fn!(*const [u64; 32], *mut [u64; 10], u64, *const u8, usize);
/// `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`, on the key's
/// context.
type StreamCryptFn = asm_fn!(
    *const KeyCtx,
    usize,
    *mut [u64; 10],
    u64,
    u64,
    *mut u8,
    usize
);
/// `vg_aes_gcm_stream_finish`.
type StreamFinishFn = asm_fn!(
    *const [u64; 32],
    usize,
    *mut [u64; 10],
    u64,
    u64,
    *mut [u8; 16]
);
/// `vg_aes_gcm_stream_verify`.
type StreamVerifyFn =
    asm_fn!(*const [u64; 32], usize, *mut [u64; 10], u64, u64, *const u8, usize => u32);

/// An instance that reads the key context of `vg_aes_gcm_init`, as a
/// function on the key's context (`KeyCtx`), which begins with it: on x86-64
/// with prepared contexts, its pointer type converted. Raw pointers to sized
/// types are ABI-compatible, so calling the function through the converted
/// pointer is calling it (Rust reference, "Function pointer ABI
/// compatibility"), and it reads only the first 256 bytes of the context.
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
macro_rules! on_key_ctx {
    ($f:expr, $($a:ty),* $(=> $r:ty)?; $t:ty) => {
        // SAFETY: as above; the two types differ only in the pointee type of
        // the first argument.
        unsafe { core::mem::transmute::<asm_fn!(*const [u64; 32] $(, $a)* $(=> $r)?), $t>($f) }
    };
}
#[cfg(not(all(target_arch = "x86_64", feature = "alloc")))]
macro_rules! on_key_ctx {
    ($f:expr, $($a:ty),* $(=> $r:ty)?; $t:ty) => {
        $f
    };
}

/// The functions a key calls: one backend's instances, chosen once, in
/// `AesGcm::new` (`Backend::fns`). On x86-64, for a backend whose
/// `_prepared` instances the CPU runs (`Backend::prepared`), those in place
/// of `seal`, `open`, `seal_gather` and the streaming updates, with the key
/// setup `new` calls (`prepare`); on AArch64, for a backend with
/// `_with_powers` instances, those (`powers`).
struct Fns {
    /// The backend whose instances these are.
    #[cfg(test)]
    backend: Backend,
    init: InitFn,
    seal: SealFn,
    open: OpenFn,
    seal_gather: SealGatherFn,
    stream_init: StreamInitFn,
    stream_aad: StreamAadFn,
    stream_encrypt: StreamCryptFn,
    stream_decrypt: StreamCryptFn,
    stream_finish: StreamFinishFn,
    stream_verify: StreamVerifyFn,
    /// `vg_aes_gcm_prepare`, which makes the prepared context from the key
    /// context of `vg_aes_gcm_init`, for the `_prepared` instances.
    #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
    prepare: Option<Prepare>,
    /// The bytes of the key context `new` writes, and `drop` wipes:
    /// `vg_aes_gcm_init`'s 256, or those `prepare` writes (its proven
    /// `_CTX_WRITTEN`, or all of them).
    #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
    written: usize,
    /// On AArch64, the `_with_powers` instances of `seal` and `open`, which
    /// read the powers `AesGcm::new` stores (`AesGcm::powers`).
    #[cfg(target_arch = "aarch64")]
    powers: Option<Prepared>,
}

impl Backend {
    /// Its plain instances.
    const fn plain_fns(self) -> Fns {
        let stream_encrypt = on_key_ctx!(instance!(self, vg_aes_gcm_stream_encrypt,
            x86_64: [vg_aes_gcm_stream_encrypt_aesni, vg_aes_gcm_stream_encrypt_pclmul,
                vg_aes_gcm_stream_encrypt_aesni_pclmul],
            vaes: [vg_aes_gcm_stream_encrypt_vaes, vg_aes_gcm_stream_encrypt_vpclmul,
                vg_aes_gcm_stream_encrypt_vaes_pclmul, vg_aes_gcm_stream_encrypt_aesni_vpclmul,
                vg_aes_gcm_stream_encrypt_vaes_vpclmul, vg_aes_gcm_stream_encrypt_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_stream_encrypt_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_stream_encrypt_aes, vg_aes_gcm_stream_encrypt_aes_sha3]),
            usize, *mut [u64; 10], u64, u64, *mut u8, usize; StreamCryptFn);
        let stream_decrypt = on_key_ctx!(instance!(self, vg_aes_gcm_stream_decrypt,
            x86_64: [vg_aes_gcm_stream_decrypt_aesni, vg_aes_gcm_stream_decrypt_pclmul,
                vg_aes_gcm_stream_decrypt_aesni_pclmul],
            vaes: [vg_aes_gcm_stream_decrypt_vaes, vg_aes_gcm_stream_decrypt_vpclmul,
                vg_aes_gcm_stream_decrypt_vaes_pclmul, vg_aes_gcm_stream_decrypt_aesni_vpclmul,
                vg_aes_gcm_stream_decrypt_vaes_vpclmul, vg_aes_gcm_stream_decrypt_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_stream_decrypt_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_stream_decrypt_aes, vg_aes_gcm_stream_decrypt_aes_sha3]),
            usize, *mut [u64; 10], u64, u64, *mut u8, usize; StreamCryptFn);
        Fns {
            #[cfg(test)]
            backend: self,
            init: instance!(self, vg_aes_gcm_init,
                x86_64: [vg_aes_gcm_init_aesni, vg_aes_gcm_init_pclmul, vg_aes_gcm_init_aesni_pclmul],
                vaes: [vg_aes_gcm_init_vaes, vg_aes_gcm_init_vpclmul, vg_aes_gcm_init_vaes_pclmul,
                    vg_aes_gcm_init_aesni_vpclmul, vg_aes_gcm_init_vaes_vpclmul,
                    vg_aes_gcm_init_vaes_vpclmul_avx512],
                avx: [vg_aes_gcm_init_aesni_pclmul_avx],
                aarch64: [vg_aes_gcm_init_aes, vg_aes_gcm_init_aes_sha3]),
            seal: on_key_ctx!(instance!(self, vg_aes_gcm_seal,
                x86_64: [vg_aes_gcm_seal_aesni, vg_aes_gcm_seal_pclmul, vg_aes_gcm_seal_aesni_pclmul],
                vaes: [vg_aes_gcm_seal_vaes, vg_aes_gcm_seal_vpclmul, vg_aes_gcm_seal_vaes_pclmul,
                    vg_aes_gcm_seal_aesni_vpclmul, vg_aes_gcm_seal_vaes_vpclmul,
                    vg_aes_gcm_seal_vaes_vpclmul_avx512],
                avx: [vg_aes_gcm_seal_aesni_pclmul_avx],
                aarch64: [vg_aes_gcm_seal_aes, vg_aes_gcm_seal_aes_sha3]),
                usize, *const u8, usize, *const u8, usize, *mut u8, usize, *mut [u8; 16]; SealFn),
            open: on_key_ctx!(instance!(self, vg_aes_gcm_open,
                x86_64: [vg_aes_gcm_open_aesni, vg_aes_gcm_open_pclmul, vg_aes_gcm_open_aesni_pclmul],
                vaes: [vg_aes_gcm_open_vaes, vg_aes_gcm_open_vpclmul, vg_aes_gcm_open_vaes_pclmul,
                    vg_aes_gcm_open_aesni_vpclmul, vg_aes_gcm_open_vaes_vpclmul,
                    vg_aes_gcm_open_vaes_vpclmul_avx512],
                avx: [vg_aes_gcm_open_aesni_pclmul_avx],
                aarch64: [vg_aes_gcm_open_aes, vg_aes_gcm_open_aes_sha3]),
                usize, *const u8, usize, *const u8, usize, *mut u8, usize, *const u8, usize => u32;
                OpenFn),
            seal_gather: on_key_ctx!(instance!(self, vg_aes_gcm_seal_gather,
                x86_64: [vg_aes_gcm_seal_gather_aesni, vg_aes_gcm_seal_gather_pclmul,
                    vg_aes_gcm_seal_gather_aesni_pclmul],
                vaes: [vg_aes_gcm_seal_gather_vaes, vg_aes_gcm_seal_gather_vpclmul,
                    vg_aes_gcm_seal_gather_vaes_pclmul, vg_aes_gcm_seal_gather_aesni_vpclmul,
                    vg_aes_gcm_seal_gather_vaes_vpclmul, vg_aes_gcm_seal_gather_vaes_vpclmul_avx512],
                avx: [vg_aes_gcm_seal_gather_aesni_pclmul_avx],
                aarch64: [vg_aes_gcm_seal_gather_aes, vg_aes_gcm_seal_gather_aes_sha3]),
                usize, *const u8, usize, *const u8, usize, *const [usize; 2], usize, *mut u8, usize,
                *mut [u8; 16]; SealGatherFn),
            stream_init: instance!(self, vg_aes_gcm_stream_init,
                x86_64: [vg_aes_gcm_stream_init_aesni, vg_aes_gcm_stream_init_pclmul,
                    vg_aes_gcm_stream_init_aesni_pclmul],
                vaes: [vg_aes_gcm_stream_init_vaes, vg_aes_gcm_stream_init_vpclmul,
                    vg_aes_gcm_stream_init_vaes_pclmul, vg_aes_gcm_stream_init_aesni_vpclmul,
                    vg_aes_gcm_stream_init_vaes_vpclmul, vg_aes_gcm_stream_init_vaes_vpclmul_avx512],
                avx: [vg_aes_gcm_stream_init_aesni_pclmul_avx],
                aarch64: [vg_aes_gcm_stream_init_aes, vg_aes_gcm_stream_init_aes_sha3]),
            stream_aad: instance!(self, vg_aes_gcm_stream_aad,
                x86_64: [vg_aes_gcm_stream_aad_aesni, vg_aes_gcm_stream_aad_pclmul,
                    vg_aes_gcm_stream_aad_aesni_pclmul],
                vaes: [vg_aes_gcm_stream_aad_vaes, vg_aes_gcm_stream_aad_vpclmul,
                    vg_aes_gcm_stream_aad_vaes_pclmul, vg_aes_gcm_stream_aad_aesni_vpclmul,
                    vg_aes_gcm_stream_aad_vaes_vpclmul, vg_aes_gcm_stream_aad_vaes_vpclmul_avx512],
                avx: [vg_aes_gcm_stream_aad_aesni_pclmul_avx],
                aarch64: [vg_aes_gcm_stream_aad_aes, vg_aes_gcm_stream_aad_aes_sha3]),
            stream_encrypt,
            stream_decrypt,
            stream_finish: instance!(self, vg_aes_gcm_stream_finish,
                x86_64: [vg_aes_gcm_stream_finish_aesni, vg_aes_gcm_stream_finish_pclmul,
                    vg_aes_gcm_stream_finish_aesni_pclmul],
                vaes: [vg_aes_gcm_stream_finish_vaes, vg_aes_gcm_stream_finish_vpclmul,
                    vg_aes_gcm_stream_finish_vaes_pclmul, vg_aes_gcm_stream_finish_aesni_vpclmul,
                    vg_aes_gcm_stream_finish_vaes_vpclmul, vg_aes_gcm_stream_finish_vaes_vpclmul_avx512],
                avx: [vg_aes_gcm_stream_finish_aesni_pclmul_avx],
                aarch64: [vg_aes_gcm_stream_finish_aes, vg_aes_gcm_stream_finish_aes_sha3]),
            stream_verify: instance!(self, vg_aes_gcm_stream_verify,
                x86_64: [vg_aes_gcm_stream_verify_aesni, vg_aes_gcm_stream_verify_pclmul,
                    vg_aes_gcm_stream_verify_aesni_pclmul],
                vaes: [vg_aes_gcm_stream_verify_vaes, vg_aes_gcm_stream_verify_vpclmul,
                    vg_aes_gcm_stream_verify_vaes_pclmul, vg_aes_gcm_stream_verify_aesni_vpclmul,
                    vg_aes_gcm_stream_verify_vaes_vpclmul, vg_aes_gcm_stream_verify_vaes_vpclmul_avx512],
                avx: [vg_aes_gcm_stream_verify_aesni_pclmul_avx],
                aarch64: [vg_aes_gcm_stream_verify_aes, vg_aes_gcm_stream_verify_aes_sha3]),
            #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
            prepare: None,
            #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
            written: size_of::<[u64; 32]>(),
            #[cfg(target_arch = "aarch64")]
            powers: None,
        }
    }
}

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
impl Fns {
    /// These functions, with the `_prepared` instances `p` in place of
    /// `seal`, `open`, `seal_gather` and the streaming updates, and its key
    /// setup.
    const fn with(self, p: &Prepared) -> Fns {
        Fns {
            seal: p.seal,
            open: p.open,
            seal_gather: p.seal_gather,
            stream_encrypt: p.stream_encrypt,
            stream_decrypt: p.stream_decrypt,
            prepare: Some(p.prepare),
            written: p.written,
            ..self
        }
    }
}

static FNS_SCALAR: Fns = Backend::Scalar.plain_fns();
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
static FNS_AESNI: Fns = Backend::AesNi.plain_fns();
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
static FNS_PCLMUL: Fns = Backend::Pclmul.plain_fns();
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
static FNS_AESNI_PCLMUL: Fns = Backend::AesNiPclmul.plain_fns();
#[cfg(target_arch = "x86_64")]
static FNS_VAES: Fns = Backend::Vaes.plain_fns();
#[cfg(target_arch = "x86_64")]
static FNS_VPCLMUL: Fns = Backend::Vpclmul.plain_fns();
#[cfg(target_arch = "x86_64")]
static FNS_VAES_PCLMUL: Fns = Backend::VaesPclmul.plain_fns();
#[cfg(target_arch = "x86_64")]
static FNS_AESNI_VPCLMUL: Fns = Backend::AesNiVpclmul.plain_fns();
#[cfg(target_arch = "x86_64")]
static FNS_VAES_VPCLMUL: Fns = Backend::VaesVpclmul.plain_fns();
#[cfg(target_arch = "x86_64")]
static FNS_VAES_VPCLMUL_AVX512: Fns = Backend::VaesVpclmulAvx512.plain_fns();
#[cfg(target_arch = "x86_64")]
static FNS_AESNI_PCLMUL_AVX: Fns = Backend::AesNiPclmulAvx.plain_fns();
#[cfg(target_arch = "aarch64")]
static FNS_AES: Fns = Fns {
    powers: Some(PREPARED_AES),
    ..Backend::Aes.plain_fns()
};
#[cfg(target_arch = "aarch64")]
static FNS_AES_SHA3: Fns = Fns {
    powers: Some(PREPARED_AES_SHA3),
    ..Backend::AesSha3.plain_fns()
};
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
static FNS_VAES_VPCLMUL_PREPARED: Fns = Backend::VaesVpclmul
    .plain_fns()
    .with(&PREPARED_VAES_VPCLMUL);
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
static FNS_VAES_VPCLMUL_AVX512_PREPARED: Fns = Backend::VaesVpclmulAvx512
    .plain_fns()
    .with(&PREPARED_VAES_VPCLMUL_AVX512);
#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
static FNS_AESNI_PCLMUL_AVX_PREPARED: Fns = Backend::AesNiPclmulAvx
    .plain_fns()
    .with(&PREPARED_AESNI_PCLMUL_AVX);

impl Backend {
    /// The functions a key of this backend calls: on x86-64, its
    /// `_prepared` instances if a CPU with the features `f` runs them
    /// (`Backend::prepared`).
    fn fns(self, f: Features) -> &'static Fns {
        // Elsewhere no backend has `_prepared` instances in `Fns`.
        #[cfg(not(all(target_arch = "x86_64", feature = "alloc")))]
        let _ = f;
        // `with` if the CPU runs this backend's `_prepared` instances.
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        let or_prepared = |plain: &'static Fns, with: &'static Fns| {
            if self.prepared(f).is_some() {
                with
            } else {
                plain
            }
        };
        match self {
            Backend::Scalar => &FNS_SCALAR,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNi => &FNS_AESNI,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::Pclmul => &FNS_PCLMUL,
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Backend::AesNiPclmul => &FNS_AESNI_PCLMUL,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => &FNS_VAES,
            #[cfg(target_arch = "x86_64")]
            Backend::Vpclmul => &FNS_VPCLMUL,
            #[cfg(target_arch = "x86_64")]
            Backend::VaesPclmul => &FNS_VAES_PCLMUL,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNiVpclmul => &FNS_AESNI_VPCLMUL,
            #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
            Backend::VaesVpclmul => or_prepared(&FNS_VAES_VPCLMUL, &FNS_VAES_VPCLMUL_PREPARED),
            #[cfg(all(target_arch = "x86_64", not(feature = "alloc")))]
            Backend::VaesVpclmul => &FNS_VAES_VPCLMUL,
            #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
            Backend::VaesVpclmulAvx512 => {
                or_prepared(&FNS_VAES_VPCLMUL_AVX512, &FNS_VAES_VPCLMUL_AVX512_PREPARED)
            }
            #[cfg(all(target_arch = "x86_64", not(feature = "alloc")))]
            Backend::VaesVpclmulAvx512 => &FNS_VAES_VPCLMUL_AVX512,
            #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
            Backend::AesNiPclmulAvx => {
                or_prepared(&FNS_AESNI_PCLMUL_AVX, &FNS_AESNI_PCLMUL_AVX_PREPARED)
            }
            #[cfg(all(target_arch = "x86_64", not(feature = "alloc")))]
            Backend::AesNiPclmulAvx => &FNS_AESNI_PCLMUL_AVX,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => &FNS_AES,
            #[cfg(target_arch = "aarch64")]
            Backend::AesSha3 => &FNS_AES_SHA3,
        }
    }
}

/// The `_prepared` instances of a backend (`VG.Spec.Gcm.PreparedPowersRepr`),
/// or its `_prepared16` ones (`VG.Spec.Gcm.PreparedPowers16Repr`), whose
/// interleaved loops read the powers of the hash subkey from the key context
/// instead of computing them on every call, and the CPU features their key
/// setup needs; on AArch64, its `_with_powers` instances
/// (`VG.Spec.Gcm.Powers8Repr`), which need the backend's features alone (see
/// the tests).
#[cfg(any(
    all(target_arch = "x86_64", feature = "alloc"),
    target_arch = "aarch64"
))]
struct Prepared {
    #[cfg(target_arch = "x86_64")]
    features: Features,
    seal: SealPrepared,
    open: OpenPrepared,
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
    /// The bytes of the key context it writes (`Fns::written`).
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
use prepared_types::{OpenPrepared, SealGatherPrepared, SealPrepared};
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
    features: VG_AES_GCM_PREPARE_VPCLMUL_AVX512_FEATURES,
    seal: vg_aes_gcm_seal_prepared_vaes_vpclmul_avx512,
    open: vg_aes_gcm_open_prepared_vaes_vpclmul_avx512,
    seal_gather: vg_aes_gcm_seal_gather_prepared_vaes_vpclmul_avx512,
    stream_encrypt: vg_aes_gcm_stream_encrypt_prepared_vaes_vpclmul_avx512,
    stream_decrypt: vg_aes_gcm_stream_decrypt_prepared_vaes_vpclmul_avx512,
    prepare: vg_aes_gcm_prepare_vpclmul_avx512,
    written: size_of::<Ctx>(),
};

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
static PREPARED_VAES_VPCLMUL: Prepared = Prepared {
    features: VG_AES_GCM_PREPARE16_VPCLMUL_FEATURES,
    seal: vg_aes_gcm_seal_prepared16_vaes_vpclmul,
    open: vg_aes_gcm_open_prepared16_vaes_vpclmul,
    seal_gather: vg_aes_gcm_seal_gather_prepared16_vaes_vpclmul,
    stream_encrypt: vg_aes_gcm_stream_encrypt_prepared16_vaes_vpclmul,
    stream_decrypt: vg_aes_gcm_stream_decrypt_prepared16_vaes_vpclmul,
    prepare: vg_aes_gcm_prepare16_vpclmul,
    written: VG_AES_GCM_PREPARE16_VPCLMUL_CTX_WRITTEN,
};

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
static PREPARED_AESNI_PCLMUL_AVX: Prepared = Prepared {
    features: VG_AES_GCM_PREPARE16_PCLMUL_AVX_FEATURES,
    seal: vg_aes_gcm_seal_prepared16_aesni_pclmul_avx,
    open: vg_aes_gcm_open_prepared16_aesni_pclmul_avx,
    seal_gather: vg_aes_gcm_seal_gather_prepared16_aesni_pclmul_avx,
    stream_encrypt: vg_aes_gcm_stream_encrypt_prepared16_aesni_pclmul_avx,
    stream_decrypt: vg_aes_gcm_stream_decrypt_prepared16_aesni_pclmul_avx,
    prepare: vg_aes_gcm_prepare16_pclmul_avx,
    written: VG_AES_GCM_PREPARE16_PCLMUL_AVX_CTX_WRITTEN,
};

#[cfg(target_arch = "aarch64")]
const PREPARED_AES: Prepared = Prepared {
    seal: vg_aes_gcm_seal_with_powers_aes,
    open: vg_aes_gcm_open_with_powers_aes,
};

#[cfg(target_arch = "aarch64")]
const PREPARED_AES_SHA3: Prepared = Prepared {
    seal: vg_aes_gcm_seal_with_powers_aes_sha3,
    open: vg_aes_gcm_open_with_powers_aes_sha3,
};

#[cfg(all(target_arch = "x86_64", feature = "alloc"))]
impl Backend {
    /// Its `_prepared` instances, if it has them and a CPU with the features
    /// `f` has those of their key setup.
    fn prepared(self, f: Features) -> Option<&'static Prepared> {
        let p = match self {
            Backend::VaesVpclmulAvx512 => &PREPARED_VAES_VPCLMUL_AVX512,
            Backend::VaesVpclmul => &PREPARED_VAES_VPCLMUL,
            Backend::AesNiPclmulAvx => &PREPARED_AESNI_PCLMUL_AVX,
            Backend::AesNi
            | Backend::Pclmul
            | Backend::AesNiPclmul
            | Backend::Vaes
            | Backend::Vpclmul
            | Backend::VaesPclmul
            | Backend::AesNiVpclmul
            | Backend::Scalar => return None,
        };
        f.contains(p.features).then_some(p)
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

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid AES key length",
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
// to a cache line: the `_prepared` instances load its round keys and powers
// 16 bytes at a time, and at 8 bytes' alignment some of those loads would
// cross cache lines. Elsewhere it is the first field too: after the
// pointer `fns`, on x86 its offset in a 4-byte-aligned value left the
// compiler unable to clear it with aligned 16-byte stores in `new`, and it
// called `memset` instead (4–5% slower `new` on Zen 3).
#[cfg_attr(all(target_arch = "x86_64", feature = "alloc"), repr(C, align(64)))]
#[cfg_attr(not(all(target_arch = "x86_64", feature = "alloc")), repr(C))]
pub struct AesGcm {
    /// The key context `vg_aes_gcm_init` writes (`VG.Spec.Gcm.KeyRepr`),
    /// with the powers of the hash subkey after it on x86-64 (`KeyCtx`):
    /// its first `written()` bytes, which `new` writes; the rest is never
    /// read.
    ctx: MaybeUninit<KeyCtx>,
    rounds: usize,
    /// The functions it calls (`Backend::fns`); on x86-64, if they are a
    /// backend's `_prepared` instances (`Fns::prepare`), `ctx` holds the
    /// powers.
    fns: &'static Fns,
    /// On AArch64, the powers of the hash subkey (`VG.Spec.Gcm.Powers8Repr`)
    /// that `new` stores if `fns` has `_with_powers` instances
    /// (`Fns::powers`), which read them; zero otherwise.
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
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(Error::InvalidKeyLength);
        }
        // The features, read once: each read is a call.
        let f = detected();
        let backend = select(f);
        let mut k = AesGcm {
            ctx: MaybeUninit::uninit(),
            rounds: key.len() / 4 + 6,
            fns: backend.fns(f),
            #[cfg(target_arch = "aarch64")]
            powers: [0; size_of::<Ctx>() / 8],
        };
        // Only the key context of `vg_aes_gcm_init` is cleared first (`key`
        // reads it); `prepare` writes its proven `written` bytes of powers,
        // and the bytes after them are never read.
        // SAFETY: `k.ctx` is valid for writes of at least 256 bytes.
        unsafe { k.ctx.as_mut_ptr().cast::<[u64; 32]>().write([0; 32]) };
        // Chosen from `backend` rather than read from `k.fns`: the load
        // before the call made `new` 1–4% slower on Neoverse N2.
        let init = backend.plain_fns().init;
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 16,
        // 24 or 32; `k.ctx` is valid for reads and writes of 256 bytes. They
        // are distinct objects, so they do not overlap each other or anything
        // on the stack, or wrap around the end of the address space. The CPU
        // has the features of the implementation selected.
        unsafe { init(key.as_ptr(), key.len(), k.ctx.as_mut_ptr().cast()) };
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        if let Some(prepare) = k.fns.prepare {
            k.prepare(prepare);
        }
        #[cfg(target_arch = "aarch64")]
        if k.fns.powers.is_some() {
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
        return self.fns.written;
        #[cfg(not(all(target_arch = "x86_64", feature = "alloc")))]
        return size_of::<KeyCtx>();
    }

    /// Computes the powers of the hash subkey into `self.ctx`, after its key
    /// context, with `fns.prepare`.
    #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
    fn prepare(&mut self, prepare: Prepare) {
        // SAFETY: `self.ctx` is valid for reads and writes of 1024 bytes,
        // and overlaps nothing on the stack; its first 256 bytes are the key
        // context of `vg_aes_gcm_init` (`VG.Spec.Gcm.KeyRepr`), which
        // `vg_aes_gcm_prepare` keeps. The CPU has its features
        // (`Backend::prepared`).
        unsafe { prepare(self.ctx.as_mut_ptr()) };
    }

    /// Computes the powers of the hash subkey into `self.powers`, from the
    /// key context, with `vg_ghash_store_powers_aes`, hashing no blocks.
    #[cfg(target_arch = "aarch64")]
    fn store_powers(&mut self) {
        // It never writes its working space (`Artifact.written`), so that
        // space needs neither initializing nor wiping.
        const _: () = assert!(VG_GHASH_STORE_POWERS_AES_SCRATCH_WRITTEN == 0);
        let mut scratch = MaybeUninit::<[u64; 32]>::uninit();
        let mut y: Block = [0; 16];
        // The hash subkey, the last 16 bytes of the key context
        // (`VG.Spec.Gcm.KeyRepr`).
        let h: *const Block = self.key()[30..].as_ptr().cast();
        // SAFETY: `h` is valid for reads of 16 bytes (within `self.ctx`, which
        // `new` wrote before calling this), and
        // so is `data`, of which no block is read (`n` is 0); `y`, `scratch`
        // and `self.powers` are distinct objects, valid for reads and writes
        // of 16, 256 and 128 bytes, which overlap nothing else; none wraps
        // around the end of the address space. The CPU has the features of
        // the key's backend, which has `_with_powers` instances, whose
        // features include `vg_ghash_store_powers_aes`'s (see the tests).
        unsafe {
            vg_ghash_store_powers_aes(h, &mut y, h, 0, scratch.as_mut_ptr(), &mut self.powers)
        };
        // `y` hashed no block: it is still zero.
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
        match &self.fns.powers {
            Some(p) => return Ok(self.seal_prepared(p, nonce, aad, data)),
            None => no_powers(),
        }
        let seal = self.fns.seal;
        let mut tag: Block = [0; 16];
        // SAFETY: `self.ctx` is the key context `vg_aes_gcm_init` wrote for
        // `self.rounds` (10, 12 or 14) rounds (every implementation writes
        // the same one), valid for reads of 256 bytes, followed on x86-64,
        // when `seal` is a `_prepared` instance, by the powers
        // `vg_aes_gcm_prepare` wrote for the same key (`AesGcm::new`), valid
        // for reads of 1024 bytes in all; `nonce` and `aad` are
        // valid for reads and `data` for reads and writes of their lengths,
        // and `tag` (a local) for reads and writes of 16 bytes. They are
        // distinct objects (`data` a unique borrow), so the writable ones
        // overlap nothing else, nor anything on the stack, and none wraps
        // around the end of the address space. The CPU has the features of
        // the implementation selected.
        unsafe {
            seal(
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
        if let Some(p) = &self.fns.powers {
            return self.open_prepared(p, nonce, aad, data, tag);
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            let open = self.fns.open;
            // SAFETY: as in `encrypt_in_place`, with the received tag `tag`
            // valid for reads of its length.
            let ok = unsafe {
                open(
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
    /// `self.fns` itself for the same reason.
    #[cfg(target_arch = "x86_64")]
    #[inline(never)]
    fn open_with(
        &self,
        data: &mut [u8],
        tag: &[u8],
        nonce: &[u8],
        aad: &[u8],
    ) -> Result<(), Error> {
        let open = self.fns.open;
        // SAFETY: as in `encrypt_in_place`, with the received tag `tag`
        // valid for reads of its length.
        let ok = unsafe {
            open(
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
        #[cfg(target_arch = "aarch64")]
        if let Some(p) = &self.fns.powers {
            return Ok(self.seal_pieces_prepared(p, nonce, aad, plaintext, out));
        }
        #[cfg(all(target_arch = "powerpc64", target_endian = "little"))]
        if len >= 512 {
            return Ok(self.seal_pieces_split(nonce, aad, plaintext, out));
        }
        // The descriptors of the pieces, as `vg_aes_gcm_seal_gather` takes
        // them: each its address and its length. Only the first
        // `plaintext.len()` are written, and the function reads only those.
        let mut descs = [const { MaybeUninit::<[usize; 2]>::uninit() }; Self::MAX_PIECES];
        for (d, p) in descs.iter_mut().zip(plaintext) {
            d.write([p.as_ptr() as usize, p.len()]);
        }
        let src: *const [usize; 2] = descs.as_ptr().cast();
        // The gathering seals every shape (on x86-64, a `_prepared` one a
        // TLS record's by `vg_aes_gcm_seal_split_prepared` from the first
        // piece, before anything else).
        let f = self.fns.seal_gather;
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
        // features of the key's backend, whose `_with_powers` instance this
        // is.
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
        copy_pieces(plaintext, out);
        self.seal_prepared(p, nonce, aad, out)
    }
}

/// Copies already length-checked pieces into their shared output buffer.
#[cfg(any(
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
#[inline]
fn copy_pieces(plaintext: &[&[u8]], out: &mut [u8]) {
    let mut rest = out;
    for piece in plaintext {
        let (dst, tail) = rest.split_at_mut(piece.len());
        dst.copy_from_slice(piece);
        rest = tail;
    }
}

#[cfg(all(target_arch = "powerpc64", target_endian = "little"))]
impl AesGcm {
    /// Reads the first piece's complete blocks directly and copies its
    /// partial block and the remaining pieces into the destination suffix.
    /// `encrypt` has checked all lengths and the text is nonempty.
    fn seal_pieces_split(
        &self,
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[&[u8]],
        out: &mut [u8],
    ) -> Block {
        let first = plaintext
            .iter()
            .position(|piece| !piece.is_empty())
            .unwrap();
        let src = plaintext[first];
        let src_len = src.len() & !15;
        out[src_len..src.len()].copy_from_slice(&src[src_len..]);
        copy_pieces(&plaintext[first + 1..], &mut out[src.len()..]);
        let mut tag = [0; 16];
        // SAFETY: the key, nonce, AAD and output satisfy the same conditions
        // as `encrypt_in_place`. `src` is read only and the unique output
        // borrow makes it disjoint from the output, tag and local stack.
        // Its complete-block prefix fits the output; all later plaintext
        // bytes were copied into the output suffix above. POWER8+ supports
        // the instructions of this implementation.
        unsafe {
            vg_aes_gcm_seal_split(
                self.ctx.as_ptr(),
                self.rounds,
                nonce.as_ptr(),
                nonce.len(),
                aad.as_ptr(),
                aad.len(),
                src.as_ptr(),
                src_len,
                out.as_mut_ptr(),
                out.len(),
                &mut tag,
            )
        };
        tag
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
        let init = key.fns.stream_init;
        // SAFETY: `key.ctx` is a key context (as in
        // `AesGcm::encrypt_in_place`), valid for reads of 256 bytes, `nonce`
        // for reads of `nonce.len()`, and `s.state` for reads and writes of
        // 80. They are distinct objects, so the writable one overlaps nothing
        // else, nor anything on the stack, and none wraps around. The CPU has
        // the features of the implementation selected.
        unsafe { init(key.key(), nonce.as_ptr(), nonce.len(), &mut s.state) };
        Ok(s)
    }

    /// Absorbs more additional data, which must all come before the text.
    fn update_aad(&mut self, aad: &[u8]) -> Result<(), Error> {
        if self.in_text {
            return Err(Error::AadAfterText);
        }
        let aad_len =
            add_len(self.aad_len, aad.len(), MAX_AAD).map_err(|()| Error::InvalidAadLength)?;
        let f = self.key.fns.stream_aad;
        // SAFETY: as in `new`; `self.state` represents a message with
        // `self.aad_len` bytes of additional data and no text yet.
        unsafe {
            f(
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
        let fns = self.key.fns;
        let f = if DECRYPT {
            fns.stream_decrypt
        } else {
            fns.stream_encrypt
        };
        // SAFETY: as in `new`, with `data` valid for reads and writes of
        // `data.len()` bytes (a unique borrow, so it overlaps nothing else);
        // `self.state` represents a message with `self.aad_len` bytes of
        // additional data and `self.text_len` of text.
        unsafe {
            f(
                self.key.ctx.as_ptr(),
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

impl Stream<'_, false> {
    /// Finishes the message and returns its 16-byte tag.
    fn finish(mut self) -> Block {
        let f = self.key.fns.stream_finish;
        let mut tag: Block = [0; 16];
        // SAFETY: as in `update`, with `tag` (a local) valid for reads and
        // writes of 16 bytes. `update_aad` and `update` checked the lengths
        // (§5.2.1.1).
        unsafe {
            f(
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
        let f = self.key.fns.stream_verify;
        // SAFETY: as in `finish`, with the received tag `tag` valid for
        // reads of its length.
        let ok = unsafe {
            f(
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
    use super::{AesGcm, Backend, Error, MAX_AAD, MAX_TEXT, add_len, select};
    use crate::cpu::detected;
    use verified_garbage_cpu::Features;

    /// The implementation chosen for each set of features: AES's and
    /// GHASH's, independently.
    #[test]
    fn backend() {
        let f = |bits: u32| select(Features(bits));
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            assert_eq!(
                f(verified_garbage_cpu::feature::AES
                    | verified_garbage_cpu::feature::PCLMULQDQ
                    | verified_garbage_cpu::feature::SSSE3),
                Backend::AesNiPclmul
            );
            assert_eq!(
                f(verified_garbage_cpu::feature::AES | verified_garbage_cpu::feature::SSSE3),
                Backend::AesNi
            );
            assert_eq!(
                f(verified_garbage_cpu::feature::PCLMULQDQ | verified_garbage_cpu::feature::SSSE3),
                Backend::Pclmul
            );
        }
        // AES-NI needs SSSE3 too on x86-64 (`vg_aes_ctr32_aesni`'s byte
        // shuffles), not on x86.
        #[cfg(target_arch = "x86_64")]
        assert_eq!(
            f(verified_garbage_cpu::feature::AES | verified_garbage_cpu::feature::PCLMULQDQ),
            Backend::Scalar
        );
        // VAES and VPCLMULQDQ, each with the other, the other's 128-bit
        // instruction or neither; their 256-bit code needs AVX2 too.
        #[cfg(target_arch = "x86_64")]
        {
            let all = verified_garbage_cpu::feature::AES
                | verified_garbage_cpu::feature::AVX
                | verified_garbage_cpu::feature::AVX2
                | verified_garbage_cpu::feature::PCLMULQDQ
                | verified_garbage_cpu::feature::SSSE3
                | verified_garbage_cpu::feature::VAES
                | verified_garbage_cpu::feature::VPCLMULQDQ;
            assert_eq!(f(all), Backend::VaesVpclmul);
            // The 512-bit loops need AVX512F and AVX512BW too.
            let avx512 = all
                | verified_garbage_cpu::feature::AVX512F
                | verified_garbage_cpu::feature::AVX512BW;
            assert_eq!(f(avx512), Backend::VaesVpclmulAvx512);
            assert_eq!(
                f(all | verified_garbage_cpu::feature::AVX512F),
                Backend::VaesVpclmul
            );
            assert_eq!(
                f(all & !verified_garbage_cpu::feature::VPCLMULQDQ),
                Backend::VaesPclmul
            );
            assert_eq!(
                f(verified_garbage_cpu::feature::AES
                    | verified_garbage_cpu::feature::AVX
                    | verified_garbage_cpu::feature::AVX2
                    | verified_garbage_cpu::feature::PCLMULQDQ
                    | verified_garbage_cpu::feature::SSSE3
                    | verified_garbage_cpu::feature::VPCLMULQDQ),
                Backend::AesNiVpclmul
            );
            assert_eq!(
                f(verified_garbage_cpu::feature::AES
                    | verified_garbage_cpu::feature::AVX
                    | verified_garbage_cpu::feature::AVX2
                    | verified_garbage_cpu::feature::SSSE3
                    | verified_garbage_cpu::feature::VAES),
                Backend::Vaes
            );
            assert_eq!(
                f(verified_garbage_cpu::feature::AVX
                    | verified_garbage_cpu::feature::AVX2
                    | verified_garbage_cpu::feature::PCLMULQDQ
                    | verified_garbage_cpu::feature::SSSE3
                    | verified_garbage_cpu::feature::VPCLMULQDQ),
                Backend::Vpclmul
            );
            // AES-NI and PCLMULQDQ with AVX (and without AVX2, which the
            // 256-bit code needs): one pass.
            assert_eq!(
                f(verified_garbage_cpu::feature::AES
                    | verified_garbage_cpu::feature::AVX
                    | verified_garbage_cpu::feature::PCLMULQDQ
                    | verified_garbage_cpu::feature::SSSE3
                    | verified_garbage_cpu::feature::VAES
                    | verified_garbage_cpu::feature::VPCLMULQDQ),
                Backend::AesNiPclmulAvx
            );
            assert_eq!(
                f(verified_garbage_cpu::feature::AES
                    | verified_garbage_cpu::feature::AVX
                    | verified_garbage_cpu::feature::PCLMULQDQ
                    | verified_garbage_cpu::feature::SSSE3),
                Backend::AesNiPclmulAvx
            );
            assert_eq!(
                f(verified_garbage_cpu::feature::AES
                    | verified_garbage_cpu::feature::AVX
                    | verified_garbage_cpu::feature::SSSE3),
                Backend::AesNi
            );
        }
        #[cfg(target_arch = "x86")]
        {
            assert_eq!(f(verified_garbage_cpu::feature::AES), Backend::AesNi);
            assert_eq!(
                f(verified_garbage_cpu::feature::AES | verified_garbage_cpu::feature::PCLMULQDQ),
                Backend::AesNi
            );
        }
        #[cfg(target_arch = "aarch64")]
        {
            assert_eq!(f(verified_garbage_cpu::feature::AES), Backend::Aes);
            assert_eq!(
                f(verified_garbage_cpu::feature::AES | verified_garbage_cpu::feature::SHA3),
                Backend::AesSha3
            );
            assert_eq!(f(verified_garbage_cpu::feature::SHA3), Backend::Scalar);
        }
        assert_eq!(f(0), Backend::Scalar);
        let best = AesGcm::new(&[0; 16]).unwrap().fns.backend;
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
                        VG_AES_GCM_PREPARE16_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_SEAL_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_OPEN_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_SEAL_SPLIT_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_PREPARED16_AESNI_PCLMUL_AVX_FEATURES,
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
                        VG_AES_GCM_PREPARE16_VPCLMUL_FEATURES,
                        VG_AES_GCM_SEAL_PREPARED16_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_OPEN_PREPARED16_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_PREPARED16_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_PREPARED16_VAES_VPCLMUL_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_PREPARED16_VAES_VPCLMUL_FEATURES,
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
                        VG_AES_GCM_PREPARE_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_SEAL_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_OPEN_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_STREAM_ENCRYPT_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_SEAL_GATHER_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
                        VG_AES_GCM_STREAM_DECRYPT_PREPARED_VAES_VPCLMUL_AVX512_FEATURES,
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
                VG_AES_GCM_SEAL_WITH_POWERS_AES_FEATURES,
                VG_AES_GCM_OPEN_WITH_POWERS_AES_FEATURES,
                VG_GHASH_STORE_POWERS_AES_FEATURES,
            ] {
                assert!(VG_AES_GCM_SEAL_AES_FEATURES.contains(other));
            }
            for other in [
                VG_AES_GCM_INIT_AES_SHA3_FEATURES,
                VG_AES_GCM_OPEN_AES_SHA3_FEATURES,
                VG_AES_GCM_STREAM_INIT_AES_SHA3_FEATURES,
                VG_AES_GCM_STREAM_AAD_AES_SHA3_FEATURES,
                VG_AES_GCM_STREAM_ENCRYPT_AES_SHA3_FEATURES,
                VG_AES_GCM_STREAM_DECRYPT_AES_SHA3_FEATURES,
                VG_AES_GCM_STREAM_FINISH_AES_SHA3_FEATURES,
                VG_AES_GCM_STREAM_VERIFY_AES_SHA3_FEATURES,
                VG_AES_GCM_SEAL_GATHER_AES_SHA3_FEATURES,
                VG_AES_GCM_SEAL_AES_SHA3_FEATURES,
                VG_AES_GCM_OPEN_WITH_POWERS_AES_SHA3_FEATURES,
                VG_GHASH_STORE_POWERS_AES_FEATURES,
            ] {
                assert!(VG_AES_GCM_SEAL_WITH_POWERS_AES_SHA3_FEATURES.contains(other));
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

    /// The backends with `_prepared` (on AArch64, `_with_powers`) instances.
    #[cfg(any(
        all(target_arch = "x86_64", feature = "alloc"),
        target_arch = "aarch64"
    ))]
    const PREPARED: &[Backend] = &[
        #[cfg(target_arch = "x86_64")]
        Backend::VaesVpclmulAvx512,
        #[cfg(target_arch = "x86_64")]
        Backend::VaesVpclmul,
        #[cfg(target_arch = "x86_64")]
        Backend::AesNiPclmulAvx,
        #[cfg(target_arch = "aarch64")]
        Backend::AesSha3,
        #[cfg(target_arch = "aarch64")]
        Backend::Aes,
    ];

    /// Whether this CPU runs `b` with its `_prepared` (or `_with_powers`)
    /// instances, and their key setup.
    #[cfg(any(
        all(target_arch = "x86_64", feature = "alloc"),
        target_arch = "aarch64"
    ))]
    fn runs_prepared(b: Backend) -> bool {
        #[cfg(target_arch = "x86_64")]
        let prepared = b.prepared(detected()).is_some();
        #[cfg(target_arch = "aarch64")]
        let prepared = b.fns(detected()).powers.is_some();
        detected().contains(b.features()) && prepared
    }

    impl AesGcm {
        /// The same key, with `backend`'s instances.
        fn with_backend(&self, backend: Backend) -> AesGcm {
            let mut k = self.clone();
            k.fns = backend.fns(detected());
            // On x86-64, the powers `backend` computes, if the backend `new`
            // chose has no `_prepared` instances (VAES without VPCLMULQDQ
            // chooses `VaesPclmul`, and `AesNiPclmulAvx` runs) or prepares
            // another number of them (AVX-512 all 48, VAES-256 16): from the
            // key context alone, as `new` would with `backend`.
            #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
            if !matches!(
                (self.fns.prepare, k.fns.prepare),
                (Some(old), Some(new)) if core::ptr::fn_addr_eq(old, new)
            ) {
                // The old powers, which `drop` wipes only up to the new
                // backend's `written`.
                let key = size_of::<[u64; 32]>();
                // SAFETY: `k.ctx` is valid for writes of `self.written()`
                // bytes, at least `key`.
                unsafe {
                    crate::zeroize::zeroize_raw(
                        k.ctx.as_mut_ptr().cast::<u8>().add(key),
                        self.written() - key,
                    );
                }
                if let Some(prepare) = k.fns.prepare {
                    k.prepare(prepare);
                }
            }
            // On AArch64, the powers if `backend` reads them (as `new`
            // stores them), and none otherwise.
            #[cfg(target_arch = "aarch64")]
            {
                k.powers = [0; 16];
                if k.fns.powers.is_some() {
                    k.store_powers();
                }
            }
            k
        }

        /// The words of the key context that `new` wrote.
        #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
        fn written_ctx(&self) -> &[u64] {
            // SAFETY: `new` wrote the first `written()` bytes of `self.ctx`,
            // a multiple of 8.
            unsafe { core::slice::from_raw_parts(self.ctx.as_ptr().cast(), self.written() / 8) }
        }
    }

    /// Every implementation the CPU can run encrypts and decrypts long
    /// messages (whole groups of 16 blocks, which some implementations
    /// interleave, and the blocks left) as the baseline one does, one-shot
    /// and streaming.
    #[test]
    fn backends_agree() {
        let msg: [u8; 3100] = core::array::from_fn(|i| (i * 13 + 1) as u8);
        let aad = [9u8; 7];
        let nonce = [2u8; 12];
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&[0x5a; 32][..key_len]).unwrap();
            let base = k.with_backend(Backend::Scalar);
            for &(b, _) in Backend::ALL
                .iter()
                .filter(|(_, need)| detected().contains(*need))
            {
                let k = k.with_backend(b);
                // `encrypt` copies texts shorter than 768 bytes and seals
                // them in place, and streams longer ones, on the backends
                // with out-of-place interleaved loops.
                for len in [256, 300, 512, 767, 768, 769, 1024, 1300, 3072] {
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
                    let (p, t) = msg[..len].split_at(len - 1);
                    // Slices after one ending inside a block: shorter than
                    // the bytes that end it, ending it exactly, and longer.
                    let m = &msg[..len];
                    let short: [&[u8]; 4] = [&m[..5], &m[5..7], &m[7..16], &m[16..]];
                    let ends: [&[u8]; 3] = [&m[..1], &m[1..32], &m[32..]];
                    let long: [&[u8]; 3] = [&m[..3], &m[3..len - 33], &m[len - 33..]];
                    for pieces in [&[m][..], &[a, c], &[p, t], &short, &ends, &long] {
                        let mut out = [0u8; 3100];
                        let tag = k.encrypt(&nonce, &aad, pieces, &mut out[..len]);
                        assert_eq!((&out[..len], tag), (&want[..len], Ok(want_tag)), "{b:?}");
                    }
                }
            }
        }
    }

    /// Long texts with every number of bytes after their whole blocks, after
    /// additional data of none, part of and whole blocks, encrypt as the
    /// baseline does on every backend the CPU can run.
    #[test]
    fn long_tails_agree() {
        let msg: [u8; 1040] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        let aad = [0x33u8; 16];
        let nonce = [4u8; 12];
        for key_len in [16, 32] {
            let k = AesGcm::new(&[0x6b; 32][..key_len]).unwrap();
            let base = k.with_backend(Backend::Scalar);
            for &(b, _) in Backend::ALL
                .iter()
                .filter(|(_, need)| detected().contains(*need))
            {
                let k = k.with_backend(b);
                for al in [0, 13, 16] {
                    for len in 1024..=1040 {
                        let mut want = msg;
                        let want_tag = base
                            .encrypt_in_place(&nonce, &aad[..al], &mut want[..len])
                            .unwrap();
                        let mut ct = msg;
                        let tag = k
                            .encrypt_in_place(&nonce, &aad[..al], &mut ct[..len])
                            .unwrap();
                        assert_eq!((&ct[..len], tag), (&want[..len], want_tag), "{b:?}");
                    }
                }
            }
        }
    }

    /// Every number of whole blocks from 16 to 41, alone or with part of a
    /// block after them, encrypts as the baseline does on every backend the
    /// CPU can run, for each key size: interleaved loops that take every
    /// block from 16 on end with each number of blocks left over.
    #[test]
    fn block_counts_agree() {
        let msg: [u8; 661] = core::array::from_fn(|i| (i * 11 + 5) as u8);
        let nonce = [6u8; 12];
        for key_len in [16, 24, 32] {
            let k = AesGcm::new(&[0x2d; 32][..key_len]).unwrap();
            let base = k.with_backend(Backend::Scalar);
            for &(b, _) in Backend::ALL
                .iter()
                .filter(|(_, need)| detected().contains(*need))
            {
                let k = k.with_backend(b);
                for len in (256..=656).step_by(16).flat_map(|l| [l, l + 5]) {
                    let mut want = msg;
                    let want_tag = base
                        .encrypt_in_place(&nonce, b"", &mut want[..len])
                        .unwrap();
                    let mut ct = msg;
                    let tag = k.encrypt_in_place(&nonce, b"", &mut ct[..len]).unwrap();
                    assert_eq!((&ct[..len], tag), (&want[..len], want_tag), "{b:?}");
                }
            }
        }
    }

    /// All partial tails, including no tail and a suffix completing a
    /// block, agree with the existing in-place AEAD on every backend.
    #[cfg(all(
        any(target_arch = "x86_64", target_arch = "aarch64"),
        feature = "alloc"
    ))]
    #[test]
    fn prepared_gather_tails() {
        for key_len in [16, 24, 32] {
            let key = &[0x39; 32][..key_len];
            let reference = AesGcm::new(key).unwrap();
            for &(backend, features) in Backend::ALL {
                if !detected().contains(features) {
                    continue;
                }
                let cipher = AesGcm::new(key).unwrap().with_backend(backend);
                let nonce = [0x71; 12];
                for len in [15, 16, 17, 31, 32, 47, 48, 63, 64]
                    .into_iter()
                    .chain(256..272)
                    .chain([511, 512, 767, 768, 4097, 9995, 10000, 16384])
                {
                    let plain: alloc::vec::Vec<u8> =
                        (0..len).map(|i| (i * 37 + 11) as u8).collect();
                    for aad_len in [0, 5, 16, 17] {
                        let aad = &[0x49; 17][..aad_len];
                        for suffix_len in [0, 1, 2] {
                            let suffix = &[0x17; 2][..suffix_len];
                            let mut expected = plain.clone();
                            expected.extend_from_slice(suffix);
                            let tag = reference
                                .encrypt_in_place(&nonce, aad, &mut expected)
                                .unwrap();
                            let mut actual = alloc::vec![0x99; expected.len()];
                            let pieces = [&plain[..], suffix];
                            let actual_tag =
                                cipher.encrypt(&nonce, aad, &pieces, &mut actual).unwrap();
                            assert_eq!((&actual, actual_tag), (&expected, tag));
                        }
                    }
                }
            }
        }
    }

    /// `Backend::fns` gives a backend's `_prepared` table only to a CPU that
    /// runs their key setup (every CPU that runs the backend, so far), and
    /// that table is `Fns::with` (which the statics otherwise run only at
    /// compile time).
    #[cfg(all(target_arch = "x86_64", feature = "alloc"))]
    #[test]
    fn fns() {
        use super::{
            FNS_AESNI_PCLMUL_AVX, FNS_AESNI_PCLMUL_AVX_PREPARED, PREPARED_AESNI_PCLMUL_AVX,
        };
        use core::ptr::{eq, fn_addr_eq};
        let (b, p) = (Backend::AesNiPclmulAvx, &PREPARED_AESNI_PCLMUL_AVX);
        assert!(eq(b.fns(Features(0)), &FNS_AESNI_PCLMUL_AVX));
        assert!(eq(b.fns(b.features()), &FNS_AESNI_PCLMUL_AVX_PREPARED));
        let with = b.plain_fns().with(p);
        assert!(fn_addr_eq(with.seal, p.seal));
        assert!(fn_addr_eq(with.open, p.open));
        assert!(fn_addr_eq(with.seal_gather, p.seal_gather));
        assert!(fn_addr_eq(with.stream_encrypt, p.stream_encrypt));
        assert!(fn_addr_eq(with.stream_decrypt, p.stream_decrypt));
        assert!(with.prepare.is_some_and(|f| fn_addr_eq(f, p.prepare)));
    }

    /// Prepared contexts agree with fresh contexts around both interleaved
    /// loop widths, including partial blocks and input in one to three
    /// pieces.
    #[cfg(all(
        any(target_arch = "x86_64", target_arch = "aarch64"),
        feature = "alloc"
    ))]
    #[test]
    fn prepared_boundaries() {
        for &b in PREPARED {
            if !runs_prepared(b) {
                continue;
            }
            for key_len in [16, 24, 32] {
                let key = &[0x63; 32][..key_len];
                let warm = AesGcm::new(key).unwrap().with_backend(b);
                let base = AesGcm::new(key).unwrap().with_backend(Backend::Scalar);
                for len in [
                    0, 1, 15, 16, 17, 100, 255, 256, 257, 288, 481, 511, 512, 513, 767, 768, 769,
                    1024, 1535, 1536, 2048, 2303, 2304, 2305, 3071, 3072, 3073, 4097, 10000,
                ] {
                    let plain: alloc::vec::Vec<u8> = (0..len).map(|i| (i * 29 + 7) as u8).collect();
                    for nonce_len in [12, 13] {
                        let nonce = &[0x41; 13][..nonce_len];
                        for aad_len in [0, 5, 16, 17] {
                            let aad = &[0x23; 17][..aad_len];
                            let mut want = plain.clone();
                            let want_tag = base.encrypt_in_place(nonce, aad, &mut want).unwrap();
                            let mut actual = plain.clone();
                            let tag = warm.encrypt_in_place(nonce, aad, &mut actual).unwrap();
                            assert_eq!((&actual, tag), (&want, want_tag));
                            warm.decrypt_in_place(nonce, aad, &mut actual, &tag)
                                .unwrap();
                            assert_eq!(actual, plain);
                            // A truncated tag, by the same path.
                            actual.clone_from(&want);
                            let short_tag: &[u8; 12] = tag[..12].try_into().unwrap();
                            warm.decrypt_in_place_truncated(nonce, aad, &mut actual, short_tag)
                                .unwrap();
                            assert_eq!(actual, plain);
                            // A wrong tag leaves the ciphertext as it was.
                            let mut bad_tag = tag;
                            bad_tag[15] ^= 1;
                            actual.clone_from(&want);
                            assert!(
                                warm.decrypt_in_place(nonce, aad, &mut actual, &bad_tag)
                                    .is_err()
                            );
                            assert_eq!(actual, want);
                            // The pieces below split off up to 17 bytes.
                            if len < 17 {
                                continue;
                            }
                            // One piece (the gathering's path for TLS
                            // records; on 512-bit registers from 256
                            // bytes); a second of 1 byte (the same, a TLS
                            // 1.3 record's content type), none (the
                            // same, a TLS 1.2 record's), 16 bytes (the same
                            // when the first ends on a block), or 17;
                            // three; empty
                            // pieces around and between them (which AArch64
                            // copies as it does the others); and as many
                            // pieces as `encrypt` takes.
                            let (a, b) = plain.split_at(len - 17);
                            let (b, c) = b.split_at(1);
                            let many: alloc::vec::Vec<&[u8]> =
                                plain.chunks(len.div_ceil(AesGcm::MAX_PIECES)).collect();
                            let ways: [&[&[u8]]; 8] = [
                                &[&plain],
                                &[&plain[..len - 1], &plain[len - 1..]],
                                &[&plain, &[]],
                                &[&plain[..len - 16], &plain[len - 16..]],
                                &[a, &plain[len - 17..]],
                                &[a, b, c],
                                &[&[], a, &[], &[], b, c, &[]],
                                &many,
                            ];
                            for pieces in ways {
                                actual.fill(0);
                                let tag = warm.encrypt(nonce, aad, pieces, &mut actual).unwrap();
                                assert_eq!((&actual, tag), (&want, want_tag));
                            }
                        }
                    }
                }
            }
        }
    }

    /// A key whose backend has `_prepared` (on AArch64, `_with_powers`)
    /// instances computes the powers of its hash subkey when it is created:
    /// on x86-64 after the key context of `vg_aes_gcm_init`, which the plain
    /// functions read alike, and on AArch64 next to it; a key whose backend
    /// has none does not. Either encrypts and decrypts every length,
    /// one-shot, out of place and streaming, as the baseline does, and a
    /// clone keeps the powers.
    #[cfg(any(
        all(target_arch = "x86_64", feature = "alloc"),
        target_arch = "aarch64"
    ))]
    #[test]
    fn eager_powers() {
        let msg: [u8; 700] = core::array::from_fn(|i| (i * 11 + 5) as u8);
        let aad = [3u8; 5];
        let nonce = [7u8; 12];
        for key_len in [16, 24, 32] {
            let key = &[0x3c; 32][..key_len];
            let fresh = AesGcm::new(key).unwrap();
            #[cfg(target_arch = "x86_64")]
            {
                assert_eq!(
                    fresh.fns.prepare.is_some(),
                    fresh.fns.backend.prepared(detected()).is_some()
                );
                if fresh.fns.prepare.is_none() {
                    assert_eq!(fresh.written(), size_of::<[u64; 32]>());
                }
            }
            #[cfg(target_arch = "aarch64")]
            assert_eq!(
                fresh.powers.iter().all(|&w| w == 0),
                fresh.fns.powers.is_none()
            );
            let base = fresh.with_backend(Backend::Scalar);
            #[cfg(target_arch = "x86_64")]
            assert!(base.fns.prepare.is_none());
            #[cfg(target_arch = "aarch64")]
            assert!(base.fns.powers.is_none() && base.powers == [0; 16]);
            for &b in PREPARED {
                if !runs_prepared(b) {
                    continue;
                }
                let k = AesGcm::new(key).unwrap().with_backend(b);
                assert_eq!(k.key(), base.key());
                #[cfg(target_arch = "x86_64")]
                {
                    assert!(k.fns.prepare.is_some());
                    assert_eq!(k.clone().written_ctx(), k.written_ctx());
                    let mut want_powers = [0; 128];
                    want_powers[..32].copy_from_slice(base.key());
                    // SAFETY: as in `AesGcm::prepare`.
                    unsafe { (b.prepared(detected()).unwrap().prepare)(&mut want_powers) };
                    assert_eq!(k.written_ctx(), &want_powers[..k.written() / 8]);
                }
                // On AArch64, the powers are those `new` stores for the
                // backend `new` chose.
                #[cfg(target_arch = "aarch64")]
                {
                    assert!(k.fns.powers.is_some());
                    assert_eq!(k.clone().key(), k.key());
                    assert_ne!(k.powers, [0; 16]);
                    assert_eq!(k.clone().powers, k.powers);
                    // This CPU runs `b`, so `new` chose a backend with
                    // powers too, which are the same.
                    assert_eq!(fresh.powers, k.powers);
                }
                for len in [0, 1, 15, 16, 17, 63, 64, 255, 256, 300, 512, 700] {
                    let mut want = msg;
                    let want_tag = base
                        .encrypt_in_place(&nonce, &aad, &mut want[..len])
                        .unwrap();
                    let mut ct = msg;
                    let tag = k.encrypt_in_place(&nonce, &aad, &mut ct[..len]).unwrap();
                    assert_eq!((&ct[..len], tag), (&want[..len], want_tag));
                    let mut out = [0u8; 700];
                    let pieces: [&[u8]; 2] = [&msg[..len / 2], &msg[len / 2..len]];
                    let tag = k.encrypt(&nonce, &aad, &pieces, &mut out[..len]);
                    assert_eq!((&out[..len], tag), (&want[..len], Ok(want_tag)));
                    let mut e = k.encryptor(&nonce).unwrap();
                    e.update_aad(&aad).unwrap();
                    let mut st = msg;
                    e.update(&mut st[..len]).unwrap();
                    assert_eq!((&st[..len], e.finalize()), (&want[..len], want_tag));
                    let mut d = k.decryptor(&nonce).unwrap();
                    d.update_aad(&aad).unwrap();
                    d.update(&mut st[..len]).unwrap();
                    d.finalize(&want_tag).unwrap();
                    assert_eq!(&st[..len], &msg[..len]);
                    let mut bad = want_tag;
                    bad[0] ^= 1;
                    let rejected = k.decrypt_in_place(&nonce, &aad, &mut ct[..len], &bad);
                    assert_eq!(rejected, Err(Error::TagMismatch));
                    assert_eq!(&ct[..len], &want[..len]);
                    k.decrypt_in_place(&nonce, &aad, &mut ct[..len], &want_tag)
                        .unwrap();
                    assert_eq!(&ct[..len], &msg[..len]);
                }
            }
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
