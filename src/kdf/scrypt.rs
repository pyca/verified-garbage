//! scrypt (RFC 7914 §6).
//!
//! scryptROMix reads its table `V` at indices derived from the password, so its
//! memory accesses, and so its timing through the caches, depend on them, as is
//! inherent to scrypt; nothing else secret affects them.

#![cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "x86",
        target_arch = "riscv64",
        all(target_arch = "powerpc64", target_endian = "little")
    ),
    feature = "alloc"
))]

use alloc::vec::Vec;

use crate::align::CacheAligned;

use crate::arch::dispatch::scrypt::vg_scrypt_auto;
use crate::error::PasswordHashError;

/// The 128-byte chunks of working space scrypt allocates beyond ROMix's
/// `r + 2`, so that PBKDF2-HMAC-SHA256's 1,600 bytes fit in the `r + 16`
/// chunks `vg_scrypt` takes.
const PBKDF2_CHUNKS: usize = 14;

/// A zeroed vector of `len` 128-byte chunks, or `AllocationFailed`.
fn chunks(len: usize) -> Result<Vec<CacheAligned<[u8; 128]>>, PasswordHashError> {
    let mut v = Vec::new();
    v.try_reserve_exact(len)
        .map_err(|_| PasswordHashError::AllocationFailed)?;
    v.resize(len, CacheAligned([0; 128]));
    Ok(v)
}

/// Fills `out` with the key derived from `password` and `salt` by scrypt
/// with CPU/memory cost parameter `n`, block size parameter `r` and
/// parallelization parameter `p`, if that needs at most `max_memory` bytes.
///
/// scrypt needs `128 · (r · (n + p) + r + 2)` bytes: `128 · r · n` for
/// ROMix's table, `128 · r · p` for the blocks and `128 · (r + 2)` of working
/// space. For `r ≥ 2` that is at most OpenSSL's `EVP_PBE_scrypt` accounting,
/// `128 · r · (n + p + 2)` bytes. The working space also holds PBKDF2's,
/// 1,792 bytes more, which (like the stack) the limit does not count.
///
/// # Errors
///
/// [`PasswordHashError::InvalidParameters`] if the parameters or `out`'s
/// length are not valid (RFC 7914 §2 and §6: `n` must be a power of two
/// greater than 1 and less than `2^(128 r / 8)`, `r` and `p` must be
/// positive with `p ≤ (2³² − 1) · 32 / (128 r)`, and `out` must be 1 to
/// (2³² − 1) · 32 bytes long), [`PasswordHashError::MemoryLimitExceeded`] if
/// scrypt would need more than `max_memory` bytes (or more than the address
/// space), and [`PasswordHashError::AllocationFailed`] if allocating them
/// fails. `out` is unchanged then.
pub fn derive(
    password: &[u8],
    salt: &[u8],
    n: u64,
    r: u32,
    p: u32,
    max_memory: usize,
    out: &mut [u8],
) -> Result<(), PasswordHashError> {
    Memory::new(n, r, p, max_memory, out.len())?.derive(password, salt, out);
    Ok(())
}

/// Checks a password against a stored derived key: derives a key of `N`
/// bytes from `password` and `salt` by scrypt with parameters `n`, `r` and
/// `p` (as [`derive`](fn@derive) does), if that needs at most `max_memory` bytes, and
/// compares it with `expected`.
///
/// The comparison is constant time: the time taken does not depend on
/// where, or whether, the keys differ. The derivation is [`derive`](fn@derive)'s, whose
/// memory accesses depend on the password (see the module's documentation).
/// `N` is public. The derived key is wiped before returning.
///
/// `N` is a type parameter, at least 16 (a smaller one is an error when the
/// call is compiled), so that the length checked is fixed in the caller's
/// code: scrypt's keys of different lengths share their prefixes, so a key
/// checked at a length taken from a slice (a truncated stored key, or one an
/// attacker sent) would match a password on as few bytes as it has. A caller
/// with the stored key in a slice converts it (`stored.try_into()`), which
/// fails if it does not have the length the code expects.
///
/// # Errors
///
/// [`PasswordHashError::KeyMismatch`] if the derived key is not `expected`:
/// the password (or the salt or a parameter) is not the one it was derived
/// from. Otherwise as [`derive`](fn@derive), with `expected` in place of
/// `out`.
pub fn verify<const N: usize>(
    password: &[u8],
    salt: &[u8],
    n: u64,
    r: u32,
    p: u32,
    max_memory: usize,
    expected: &[u8; N],
) -> Result<(), PasswordHashError> {
    crate::ct::assert_verify_len!(N);
    let mut memory = Memory::new(n, r, p, max_memory, N)?;
    let mut key = [0u8; N];
    memory.derive(password, salt, &mut key);
    let matches = crate::ct::eq(&key, expected);
    crate::zeroize::zeroize(&mut key);
    if matches {
        Ok(())
    } else {
        Err(PasswordHashError::KeyMismatch)
    }
}

/// The memory scrypt works in, for parameters [`Memory::new`] checked,
/// wiped when it is dropped: `vg_scrypt` leaves values derived from the
/// password in it (its contract leaves its contents unspecified).
struct Memory {
    /// The block size parameter `r`.
    r: usize,
    /// The `p` blocks of `128 r` bytes.
    b: Vec<CacheAligned<[u8; 128]>>,
    /// ROMix's table, of `n` blocks.
    v: Vec<CacheAligned<[u8; 128]>>,
    /// `r + 16` chunks of working space.
    scratch: Vec<CacheAligned<[u8; 128]>>,
    /// The length of the key to derive.
    len: usize,
}

impl Memory {
    /// The memory to derive a key of `len` bytes with parameters `n`, `r`
    /// and `p` in, if they are valid and it is at most `max_memory` bytes.
    fn new(
        n: u64,
        r: u32,
        p: u32,
        max_memory: usize,
        len: usize,
    ) -> Result<Memory, PasswordHashError> {
        // RFC 7914 §2 and §6, as `VG.Spec.Scrypt.valid` states them.
        let (n64, r64, p64) = (n, u64::from(r), u64::from(p));
        let max_len = (u64::from(u32::MAX)) * 32;
        let n_ok = n64 > 1 && n64.is_power_of_two() && (r64 * 16 >= 64 || n64 < 1 << (r64 * 16));
        let p_ok = r64 > 0 && p64 > 0 && p64 <= max_len / (128 * r64);
        let len_ok = len != 0 && (len as u64) <= max_len;
        if !(n_ok && p_ok && len_ok) {
            return Err(PasswordHashError::InvalidParameters);
        }
        // `128 (r (n + p) + r + 2)` bytes, in chunks of 128.
        let size = |n: u64| usize::try_from(n).ok();
        let (n, r, p) = (size(n64), r as usize, p as usize);
        let vlen = n.and_then(|n| n.checked_mul(r));
        let total = vlen.and_then(|v| v.checked_add(r * p)?.checked_add(r + 2)?.checked_mul(128));
        let (Some(vlen), Some(total)) = (vlen, total) else {
            return Err(PasswordHashError::MemoryLimitExceeded);
        };
        if total > max_memory {
            return Err(PasswordHashError::MemoryLimitExceeded);
        }
        Ok(Memory {
            r,
            b: chunks(r * p)?,
            v: chunks(vlen)?,
            scratch: chunks(r + 2 + PBKDF2_CHUNKS)?,
            len,
        })
    }

    /// Fills `out`, of the length the memory was allocated for, with the
    /// key derived from `password` and `salt`.
    fn derive(&mut self, password: &[u8], salt: &[u8], out: &mut [u8]) {
        assert_eq!(out.len(), self.len);
        derive_by(
            password,
            salt,
            self.r,
            &mut self.b,
            &mut self.v,
            &mut self.scratch,
            out,
        );
    }
}

impl Drop for Memory {
    fn drop(&mut self) {
        fn bytes(chunks: &mut [CacheAligned<[u8; 128]>]) -> &mut [u8] {
            // SAFETY: each chunk is 128 initialized bytes with no padding.
            // The byte slice covers the same memory and borrows it exclusively.
            unsafe {
                core::slice::from_raw_parts_mut(
                    chunks.as_mut_ptr().cast(),
                    core::mem::size_of_val(chunks),
                )
            }
        }

        crate::zeroize::zeroize(bytes(&mut self.b));
        crate::zeroize::zeroize(bytes(&mut self.v));
        crate::zeroize::zeroize(bytes(&mut self.scratch));
    }
}

/// scrypt with block size parameter `r`, cost parameter `N = v.len() / r`
/// and parallelization parameter `p = b.len() / r`, for parameters that
/// [`Memory::new`] checked, with `r + 16` chunks of `scratch`.
#[allow(clippy::too_many_arguments)]
fn derive_by(
    password: &[u8],
    salt: &[u8],
    r: usize,
    b: &mut [CacheAligned<[u8; 128]>],
    v: &mut [CacheAligned<[u8; 128]>],
    scratch: &mut [CacheAligned<[u8; 128]>],
    out: &mut [u8],
) {
    // SAFETY: `r > 0`; `b.len() = r p` and `v.len() = n r` for `n`, `r`, `p`
    // and `out.len()` that are valid (`Memory::new` checked them as
    // `VG.Spec.Scrypt.valid` states them, and `out.len() ≤ (2³² − 1) · 32`),
    // and `scratch.len() = r + 16`. `password` and `salt` are valid for
    // reads of their lengths, `b`, `v` and `scratch` for reads and writes of
    // 128 bytes per chunk and `out` of its length; `b`, `v`, `scratch` and
    // `out` are distinct objects from each other and the others (`password`
    // and `salt` are only read), so none of them overlaps another written
    // one or the call's stack frame, and, as Rust objects, none wraps around
    // the address space. The dispatcher calls only an implementation the CPU
    // has the features of.
    unsafe {
        vg_scrypt_auto(
            password.as_ptr(),
            password.len(),
            salt.as_ptr(),
            salt.len(),
            r,
            b.as_mut_ptr().cast(),
            b.len(),
            v.as_mut_ptr().cast(),
            v.len(),
            scratch.as_mut_ptr().cast(),
            scratch.len(),
            out.as_mut_ptr(),
            out.len(),
        )
    };
}
