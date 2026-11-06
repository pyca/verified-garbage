//! Wiping secrets from memory the library owns.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

// What is wiped: every object holding key material (private keys, and the
// ciphers', AEADs', MACs' and hash functions' states, which hold the key under
// HMAC, PBKDF2 or keyed BLAKE2) when it is dropped; the asymmetric operations'
// intermediate values and working space (FIPS 203 §3.3, FIPS 204 §3.6.3); and
// the key the password KDFs' `verify` functions derive, once compared.
//
// What is not: the symmetric algorithms' `scratch`; the verified functions'
// stack, which their contracts do not promise to wipe (but RC4's); copies of
// states the Rust code makes on the stack when it moves them (e.g. each
// ChaCha20-Poly1305 call's context, PBKDF2's and scrypt's blocks), which later
// calls overwrite; and what is returned to the caller (a MAC, a derived key or
// a shared secret).

mod sealed {
    pub trait Sealed {}
}

/// An integer type: the value whose bytes are all zero is 0.
pub(crate) trait Int: Copy + sealed::Sealed {}

macro_rules! int {
    ($($t:ty),*) => {
        $(
            impl sealed::Sealed for $t {}
            impl Int for $t {}
        )*
    };
}
int!(u8, u16, u32, u64, i16, i32, i64);

/// Overwrites `x` with zeros using the verified assembly primitive. Its
/// opaque call prevents the compiler from removing the stores.
pub(crate) fn zeroize<T: Int>(x: &mut [T]) {
    // SAFETY: `x` is writable for its entire byte length, cannot wrap, and
    // lies outside the callee’s stack frame. All-zero bytes are valid for T.
    unsafe { zeroize_raw(x.as_mut_ptr().cast::<u8>(), core::mem::size_of_val(x)) };
}

/// Overwrites the `len` bytes at `p` with zeros, as `zeroize` does, for
/// memory that may not be initialized.
///
/// # Safety
///
/// `p` must be valid for writes of `len` bytes, which may not wrap around the
/// end of the address space or overlap the callee's stack frame.
pub(crate) unsafe fn zeroize_raw(p: *mut u8, len: usize) {
    #[cfg(target_arch = "x86_64")]
    if crate::cpu::detected().contains(crate::arch::zeroize::VG_ZEROIZE_AVX_FEATURES) {
        // SAFETY: the caller's, and the CPU has AVX, the feature
        // `vg_zeroize_avx` needs.
        unsafe { crate::arch::zeroize::vg_zeroize_avx(p, len) };
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
        return;
    }
    // SAFETY: the caller's.
    unsafe { crate::arch::zeroize::vg_zeroize(p, len) };
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

#[cfg(test)]
mod tests {
    use super::zeroize;

    #[test]
    fn zeroizes() {
        // Bytes before, between and after aligned words, at every offset and
        // every length up to 100.
        for start in 0..8 {
            for end in start..=100 {
                let mut words = [u64::MAX; 13];
                // SAFETY: `words` is 104 bytes, and any bytes are a valid `u8`.
                let bytes = unsafe { &mut *words.as_mut_ptr().cast::<[u8; 104]>() };
                zeroize(&mut bytes[start..end]);
                for (i, b) in bytes.iter().enumerate() {
                    assert_eq!(*b == 0, (start..end).contains(&i));
                }
            }
        }
        // Longer lengths, from 191 to 262 bytes, at an odd offset.
        for len in 192..=263 {
            let mut big = [u8::MAX; 264];
            zeroize(&mut big[1..len]);
            assert_eq!(big[0], u8::MAX);
            assert!(big[1..len].iter().all(|&b| b == 0));
            assert!(big[len..].iter().all(|&b| b == u8::MAX));
        }
        let mut y = [u64::MAX; 3];
        zeroize(&mut y);
        assert_eq!(y, [0; 3]);
        let mut z = [-1i16; 5];
        zeroize(&mut z);
        assert_eq!(z, [0; 5]);
    }
}
