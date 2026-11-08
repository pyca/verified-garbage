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
// the password KDFs' working memory (scrypt's and Argon2's) and the key their
// `verify` functions derive, once compared.
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

/// A type for which all-zero bytes are a valid value.
pub(crate) trait Zeroable: Copy + sealed::Sealed {}

macro_rules! int {
    ($($t:ty),*) => {
        $(
            impl sealed::Sealed for $t {}
            impl Zeroable for $t {}
        )*
    };
}
int!(u8, u16, u32, u64, i16, i32, i64);

impl<T: Zeroable, const N: usize> sealed::Sealed for [T; N] {}
impl<T: Zeroable, const N: usize> Zeroable for [T; N] {}

impl<T: Zeroable> sealed::Sealed for crate::align::CacheAligned<T> {}
impl<T: Zeroable> Zeroable for crate::align::CacheAligned<T> {}

/// Overwrites `x` with zeros using the verified assembly primitive. Its
/// opaque call prevents the compiler from removing the stores.
pub(crate) fn zeroize<T: Zeroable>(x: &mut [T]) {
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
    // SAFETY: the caller's.
    unsafe { crate::arch::dispatch::zeroize::vg_zeroize_auto(p, len) };
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

    #[test]
    fn zeroizes_arrays_and_aligned_buffers() {
        use crate::align::CacheAligned;

        let mut arrays = [[-1i16; 3]; 2];
        zeroize(&mut arrays);
        assert_eq!(arrays, [[0; 3]; 2]);

        let mut chunks = [CacheAligned([u8::MAX; 128]); 4];
        zeroize(&mut chunks[1..3]);
        assert_eq!(chunks[0].0, [u8::MAX; 128]);
        assert_eq!(chunks[1].0, [0; 128]);
        assert_eq!(chunks[2].0, [0; 128]);
        assert_eq!(chunks[3].0, [u8::MAX; 128]);

        // Include alignment padding between the arrays.
        let mut padded = [CacheAligned([u64::MAX; 3]); 4];
        zeroize(&mut padded[1..3]);
        assert_eq!(padded[0].0, [u64::MAX; 3]);
        assert_eq!(padded[1].0, [0; 3]);
        assert_eq!(padded[2].0, [0; 3]);
        assert_eq!(padded[3].0, [u64::MAX; 3]);
    }
}
