//! Public modulus setup and fixed-schedule secret exponentiation.
use crate::arch::ffdh::vg_ffdh_choose;
use crate::arch::rsa_mont::{vg_rsa_mont_mul, vg_rsa_mont_mul_adx};
use crate::rsa::{Backend, Scratch};
use alloc::{vec, vec::Vec};
use core::cmp::Ordering;

pub(super) fn canonical(a: &[u8]) -> &[u8] {
    &a[a.iter().position(|&b| b != 0).unwrap_or(a.len())..]
}
pub(super) fn bits(a: &[u8]) -> usize {
    let a = canonical(a);
    a.first()
        .map_or(0, |b| 8 * a.len() - b.leading_zeros() as usize)
}
pub(super) fn value_cmp(a: &[u8], b: &[u8]) -> Ordering {
    let (a, b) = (canonical(a), canonical(b));
    a.len().cmp(&b.len()).then_with(|| a.cmp(b))
}
pub(super) fn scalar(a: &[u8], len: usize) -> Vec<u8> {
    let a = canonical(a);
    let mut out = vec![0; len];
    out[len - a.len()..].copy_from_slice(a);
    out
}
/// Subtract one from a public odd modulus, so there is no borrow.
pub(super) fn minus_one(a: &[u8]) -> Vec<u8> {
    let mut out = a.to_vec();
    let last = out.len() - 1;
    out[last] -= 1;
    out
}

/// Public long reduction for q | p-1 checks, with a spare carry byte.
pub(super) fn divides(q: &[u8], n: &[u8]) -> bool {
    let modulus = scalar(q, q.len() + 1);
    let mut rem = vec![0u8; modulus.len()];
    for &byte in n {
        for bit in (0..8).rev() {
            let mut carry = (byte >> bit) & 1;
            for v in rem.iter_mut().rev() {
                let next = *v >> 7;
                *v = (*v << 1) | carry;
                carry = next;
            }
            if rem >= modulus {
                let mut borrow = 0u16;
                for (v, &m) in rem.iter_mut().rev().zip(modulus.iter().rev()) {
                    let sub = m as u16 + borrow;
                    borrow = u16::from((*v as u16) < sub);
                    *v = (*v as u16).wrapping_sub(sub) as u8;
                }
            }
        }
    }
    rem.iter().all(|&b| b == 0)
}

#[derive(Clone, Debug)]
pub(super) struct Montgomery {
    modulus: Vec<u64>,
    r2: Vec<u64>,
    minv: u64,
    len: usize,
    backend: Backend,
}
impl Montgomery {
    /// Only public values are used in precomputation. Works for any odd
    /// modulus >=3, including the 511-bit Sophie Germain prime of a 512-bit p.
    pub(super) fn new(p: &[u8]) -> Self {
        let w = p.len().div_ceil(8).max(2);
        let modulus = words(p, w);
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(modulus[0].wrapping_mul(inv)));
        }
        let mut r2 = vec![0u64; w];
        r2[0] = 1;
        for _ in 0..128 * w {
            double_mod(&mut r2, &modulus);
        }
        Self {
            modulus,
            r2,
            minv: inv.wrapping_neg(),
            len: p.len(),
            backend: Backend::select(crate::cpu::detected()),
        }
    }
    pub(super) fn power(&self, base: &[u8], exponent: &[u8]) -> Vec<u8> {
        let w = self.modulus.len();
        let mut ws = Scratch::new(32 + 8 * (w + 2));
        ws[6] = w as u64;
        ws[7] = self.minv;
        for j in 0..8 {
            // SAFETY: each array starts inside this stable allocation.
            ws[8 + j] = unsafe { ws.as_ptr().add(32 + j * (w + 2)) } as u64;
        }
        let at = |j| 32 + j * (w + 2);
        ws[at(0)..at(0) + w].copy_from_slice(&self.modulus);
        ws[at(1)..at(1) + w].copy_from_slice(&self.r2);
        ws[at(4)..at(4) + w].copy_from_slice(&words(base, w));
        ws[at(7)] = 1;
        self.mul(&mut ws, 4, 4, 1);
        self.mul(&mut ws, 5, 7, 1);
        // Call count and addresses depend only on public lengths. A secret
        // bit is never a branch condition, a loop bound or an array index.
        for &byte in exponent {
            for bit in (0..8).rev() {
                self.mul(&mut ws, 5, 5, 5);
                self.mul(&mut ws, 6, 5, 4);
                for i in 0..w {
                    // SAFETY: choose has no preconditions; all values secret.
                    ws[at(5) + i] = unsafe {
                        vg_ffdh_choose(ws[at(5) + i], ws[at(6) + i], u64::from((byte >> bit) & 1))
                    };
                }
            }
        }
        self.mul(&mut ws, 5, 5, 7);
        let mut out = vec![0; self.len];
        for (i, b) in out.iter_mut().rev().enumerate() {
            *b = (ws[at(5) + i / 8] >> (8 * (i % 8))) as u8;
        }
        out
    }
    fn mul(&self, ws: &mut [u64], out: u32, a: u32, b: u32) {
        let f = match self.backend {
            Backend::Baseline => vg_rsa_mont_mul,
            // IFMA is an RSA CRT optimization; its Montgomery backend is ADX.
            Backend::Adx | Backend::Ifma => vg_rsa_mont_mul_adx,
        };
        // SAFETY: ws has 32+8*(w+2) words, w>=2 and w<=128. The header
        // points into this allocation, stores the odd modulus' negative
        // inverse and w, and indices are among 1,4,5,6,7. Each b is below
        // the modulus: R², one, or a prior Montgomery result. Scratch owns
        // the writable allocation, outside the callee's stack; it is wiped
        // on drop. ADX is selected only with its generated feature set.
        unsafe { f(ws.as_mut_ptr(), ws.len(), out, a, b) }
    }
}
fn words(a: &[u8], w: usize) -> Vec<u64> {
    let mut out = vec![0; w];
    for (i, &b) in a.iter().rev().enumerate() {
        out[i / 8] |= u64::from(b) << (8 * (i % 8));
    }
    out
}
/// Public modular doubling, retaining the high carry until subtraction.
fn double_mod(a: &mut [u64], m: &[u64]) {
    let mut carry = 0;
    for v in a.iter_mut() {
        let next = *v >> 63;
        *v = (*v << 1) | carry;
        carry = next;
    }
    if carry != 0 || a.iter().rev().cmp(m.iter().rev()).is_ge() {
        let mut borrow = false;
        for (v, &modulus) in a.iter_mut().zip(m) {
            let (x, b1) = v.overflowing_sub(modulus);
            let (x, b2) = x.overflowing_sub(u64::from(borrow));
            *v = x;
            borrow = b1 | b2;
        }
    }
}
