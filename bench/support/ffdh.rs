//! AWS-LC's C FFDH API (not currently exposed by aws-lc-rs).
use aws_lc_sys as lc;
use std::ptr::{self, NonNull};

pub struct Dh(NonNull<lc::DH>);
struct BigNum(NonNull<lc::BIGNUM>);
impl BigNum {
    fn new(bytes: &[u8]) -> Self {
        // SAFETY: the input slice is readable; null requests a new allocation.
        Self(
            NonNull::new(unsafe { lc::BN_bin2bn(bytes.as_ptr(), bytes.len(), ptr::null_mut()) })
                .unwrap(),
        )
    }
    fn into_raw(self) -> *mut lc::BIGNUM {
        let p = self.0.as_ptr();
        std::mem::forget(self);
        p
    }
}
impl Drop for BigNum {
    fn drop(&mut self) {
        // SAFETY: uniquely owned allocation.
        unsafe { lc::BN_clear_free(self.0.as_ptr()) }
    }
}
impl Drop for Dh {
    fn drop(&mut self) {
        // SAFETY: uniquely owned allocation; frees its components too.
        unsafe { lc::DH_free(self.0.as_ptr()) }
    }
}
impl Dh {
    pub fn parameters(p: &[u8], g: &[u8], q: Option<&[u8]>) -> Self {
        // SAFETY: creates an owned DH allocation.
        let dh = Self(NonNull::new(unsafe { lc::DH_new() }).unwrap());
        let p = BigNum::new(p);
        let g = BigNum::new(g);
        let q = q.map(BigNum::new);
        // SAFETY: all pointers are live; successful set0 transfers ownership.
        assert_eq!(
            unsafe {
                lc::DH_set0_pqg(
                    dh.0.as_ptr(),
                    p.0.as_ptr(),
                    q.as_ref().map_or(ptr::null_mut(), |q| q.0.as_ptr()),
                    g.0.as_ptr(),
                )
            },
            1
        );
        p.into_raw();
        g.into_raw();
        if let Some(q) = q {
            q.into_raw();
        }
        dh
    }
    pub fn with_key(self, y: &[u8], x: &[u8]) -> Self {
        let y = BigNum::new(y);
        let x = BigNum::new(x);
        // SAFETY: successful set0 transfers both owned components.
        assert_eq!(
            unsafe { lc::DH_set0_key(self.0.as_ptr(), y.0.as_ptr(), x.0.as_ptr()) },
            1
        );
        y.into_raw();
        x.into_raw();
        self
    }
    pub fn generate(self) -> Self {
        // SAFETY: valid parameters in an owned DH object.
        assert_eq!(unsafe { lc::DH_generate_key(self.0.as_ptr()) }, 1);
        self
    }
    pub fn exchange(&self, peer: &Self) -> Vec<u8> {
        // SAFETY: both DH objects are live; the output has exactly DH_size bytes.
        unsafe {
            let mut out = vec![0; lc::DH_size(self.0.as_ptr()) as usize];
            assert_eq!(
                lc::DH_compute_key_padded(
                    out.as_mut_ptr(),
                    lc::DH_get0_pub_key(peer.0.as_ptr()),
                    self.0.as_ptr()
                ),
                out.len() as i32
            );
            out
        }
    }
}
