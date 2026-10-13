//! Public modulus setup and fixed-schedule secret exponentiation.
use crate::arch::ffdh::vg_ffdh_choose;
use crate::arch::rsa_mont::vg_rsa_mont_mul;
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_mont::{VG_RSA_MONT_MUL_ADX_FEATURES, vg_rsa_mont_mul_adx};
use crate::cpu::{Features, detected};
use crate::rsa::Scratch;
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

/// The Montgomery implementations FFDH calls. RSA's private-key routines
/// have additional feature requirements that do not apply to these functions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    Baseline,
    #[cfg(target_arch = "x86_64")]
    Adx,
}
impl Backend {
    fn select(_features: Features) -> Self {
        #[cfg(target_arch = "x86_64")]
        if _features.contains(VG_RSA_MONT_MUL_ADX_FEATURES) {
            return Self::Adx;
        }
        Self::Baseline
    }
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
            backend: Backend::select(detected()),
        }
    }
    pub(super) fn power(&self, base: &[u8], exponent: &[u8]) -> Vec<u8> {
        let w = self.modulus.len();
        let window = if exponent.len() >= 39 { 5 } else { 4 };
        let mut ws = self.workspace(base, (1 << window) * w);
        let at = |j| 32 + j * (w + 2);
        let table_at = at(8);
        // All window powers, including Montgomery one, in wiped storage.
        // The verified multiplication preserves this extension of the workspace.
        for i in 0..w {
            ws[table_at + i] = ws[at(5) + i];
            ws[table_at + w + i] = ws[at(4) + i];
            ws[at(6) + i] = ws[at(4) + i];
        }
        for digit in 2..(1 << window) {
            if digit % 2 == 0 {
                // Public table indices. Route even powers through squares
                // of accumulator 5, which both targets' multiplications
                // compute with their faster squaring.
                ws.copy_within(
                    table_at + (digit / 2) * w..table_at + (digit / 2 + 1) * w,
                    at(5),
                );
                self.mul(&mut ws, 5, 5, 5);
                ws.copy_within(at(5)..at(5) + w, at(6));
            } else {
                self.mul(&mut ws, 6, 6, 4);
            }
            ws.copy_within(at(6)..at(6) + w, table_at + digit * w);
        }
        ws.copy_within(table_at..table_at + w, at(5));
        // Window size and bit positions depend only on the public encoding
        // length. Every table entry is read in the same order, even for zero.
        let bits = exponent.len() * 8;
        for start in (0..bits).step_by(window) {
            let width = window.min(bits - start);
            let mut digit = 0u64;
            for bit in start..start + width {
                digit = (digit << 1) | u64::from((exponent[bit / 8] >> (7 - bit % 8)) & 1);
            }
            if start != 0 {
                for _ in 0..width {
                    self.mul(&mut ws, 5, 5, 5);
                }
            }
            let (arrays, table) = ws.split_at_mut(table_at);
            let selected = &mut arrays[at(6)..at(6) + w];
            selected.fill(0);
            for (candidate, row) in table.chunks_exact(w).enumerate() {
                // Both values are below 32: the high bit of (x-1)
                // is set exactly when x is zero.
                let equal = (digit ^ candidate as u64).wrapping_sub(1) >> 63;
                // SAFETY: choose has no preconditions. The opaque assembly
                // call returns a mask; Rust sees an arbitrary u64, so the
                // following AND/OR operations need no conditional select.
                let mask = unsafe { vg_ffdh_choose(0, u64::MAX, equal) };
                for (dst, &src) in selected.iter_mut().zip(row) {
                    *dst |= src & mask;
                }
            }
            if start == 0 {
                // The first window replaces Montgomery one directly.
                ws.copy_within(at(6)..at(6) + w, at(5));
            } else {
                self.mul(&mut ws, 5, 5, 6);
            }
        }
        self.finish(&mut ws)
    }

    /// Variable-time exponentiation for public exponents only (e.g. subgroup
    /// orders). Never use this for a private scalar or a secret prime exponent.
    pub(super) fn power_public(&self, base: &[u8], exponent: &[u8]) -> Vec<u8> {
        let mut ws = self.power_public_montgomery(base, exponent);
        self.finish(&mut ws)
    }

    fn power_public_montgomery(&self, base: &[u8], exponent: &[u8]) -> Scratch {
        let exponent = canonical(exponent);
        let window = if exponent.len() > 32 {
            5
        } else if exponent.len() > 1 {
            4
        } else {
            1
        };
        let w = self.modulus.len();
        let at = |j| 32 + j * (w + 2);
        let table_at = at(8);
        let entries = 1 << (window - 1);
        let mut ws = self.workspace(base, entries * w);
        ws.copy_within(at(4)..at(4) + w, table_at);
        if entries > 1 {
            // Odd powers: base, base^3, ...; one square supplies base^2.
            ws.copy_within(at(4)..at(4) + w, at(5));
            self.mul(&mut ws, 5, 5, 5);
            ws.copy_within(at(4)..at(4) + w, at(6));
            ws.copy_within(at(5)..at(5) + w, at(4));
            for entry in 1..entries {
                self.mul(&mut ws, 6, 6, 4);
                ws.copy_within(at(6)..at(6) + w, table_at + entry * w);
            }
            self.mul(&mut ws, 5, 7, 1);
        }
        let bit = |i: usize| (exponent[i / 8] >> (7 - i % 8)) & 1;
        let bits = exponent.len() * 8;
        let mut pos = 0;
        while pos < bits {
            if bit(pos) == 0 {
                self.mul(&mut ws, 5, 5, 5);
                pos += 1;
                continue;
            }
            let mut end = (pos + window).min(bits);
            while bit(end - 1) == 0 {
                end -= 1;
            }
            let mut digit = 0usize;
            for i in pos..end {
                self.mul(&mut ws, 5, 5, 5);
                digit = (digit << 1) | usize::from(bit(i));
            }
            // This address and the skipped multiplies depend only on the public
            // exponent. Secret exponentiation above still scans the whole table.
            let entry = table_at + (digit >> 1) * w;
            ws.copy_within(entry..entry + w, at(6));
            self.mul(&mut ws, 5, 5, 6);
            pos = end;
        }
        ws
    }

    /// One strong probable-prime witness for a public candidate p, with
    /// p-1 = d * 2^s. Keep every residue in Montgomery form until the test ends.
    pub(super) fn strong_probable_prime(&self, base: &[u8], d: &[u8], s: usize) -> bool {
        let w = self.modulus.len();
        let at = |j| 32 + j * (w + 2);
        let mut ws = self.power_public_montgomery(base, d);
        self.mul(&mut ws, 6, 7, 1);
        // Montgomery(-1) = p - Montgomery(1), since the latter is in 1..p.
        let mut negative_one = self.modulus.clone();
        let mut borrow = false;
        for (dst, &one) in negative_one.iter_mut().zip(&ws[at(6)..at(6) + w]) {
            let (v, b1) = dst.overflowing_sub(one);
            let (v, b2) = v.overflowing_sub(u64::from(borrow));
            *dst = v;
            borrow = b1 | b2;
        }
        let is_one = |ws: &[u64]| ws[at(5)..at(5) + w] == ws[at(6)..at(6) + w];
        let is_negative_one = |ws: &[u64]| ws[at(5)..at(5) + w] == negative_one;
        if is_one(&ws) || is_negative_one(&ws) {
            return true;
        }
        for _ in 1..s {
            self.mul(&mut ws, 5, 5, 5);
            if is_negative_one(&ws) {
                return true;
            }
            if is_one(&ws) {
                return false;
            }
        }
        false
    }

    fn workspace(&self, base: &[u8], table_words: usize) -> Scratch {
        let w = self.modulus.len();
        let table_at = 32 + 8 * (w + 2);
        let mut ws = Scratch::new(table_at + table_words);
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
        ws
    }

    fn finish(&self, ws: &mut [u64]) -> Vec<u8> {
        let at = |j| 32 + j * (self.modulus.len() + 2);
        self.mul(ws, 5, 5, 7);
        let mut out = vec![0; self.len];
        for (i, b) in out.iter_mut().rev().enumerate() {
            *b = (ws[at(5) + i / 8] >> (8 * (i % 8))) as u8;
        }
        out
    }
    fn mul(&self, ws: &mut [u64], out: u32, a: u32, b: u32) {
        let f = match self.backend {
            Backend::Baseline => vg_rsa_mont_mul,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_rsa_mont_mul_adx,
        };
        // SAFETY: ws has at least 32+8*(w+2) words, w>=2 and w<=128. The header
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strong_witness_matches_integer_arithmetic() {
        // An independent small-integer oracle exercises early acceptance,
        // rejection, and repeated squares, including nontrivial roots of one.
        for p in (3u64..1024).step_by(2) {
            let s = (p - 1).trailing_zeros() as usize;
            let d = (p - 1) >> s;
            let mont = Montgomery::new(&p.to_be_bytes());
            for a in [2, p / 2, p - 2] {
                let mut expected = 1;
                for _ in 0..d {
                    expected = expected * a % p;
                }
                let mut passes = expected == 1 || expected == p - 1;
                for _ in 1..s {
                    expected = expected * expected % p;
                    passes |= expected == p - 1;
                }
                assert_eq!(
                    mont.strong_probable_prime(&a.to_be_bytes(), &d.to_be_bytes(), s),
                    passes
                );
            }
        }
    }

    #[test]
    fn public_and_secret_exponents_agree() {
        // Differential checks, including zero/leading-zero exponents, every
        // window-size boundary, sparse windows, and partial modulus words.
        for bytes in [1, 8, 17, 32, 65] {
            let mont = Montgomery::new(&vec![0xff; bytes]);
            for len in [0, 1, 2, 32, 33, 39] {
                for byte in [0, 0x55, 0x80, 0xff] {
                    let exponent = vec![byte; len];
                    let mut padded = vec![0; 3];
                    padded.extend_from_slice(&exponent);
                    let expected = mont.power(&[2], &exponent);
                    assert_eq!(mont.power_public(&[2], &exponent), expected);
                    assert_eq!(mont.power_public(&[2], &padded), expected);
                }
            }
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn backend_feature_requirements() {
        // AVX, AVX2 and IFMA belong to other RSA routines: they neither
        // enable Montgomery ADX nor gate it when BMI2 and ADX are present.
        let cases: &[(&[&str], Backend)] = &[
            (&[], Backend::Baseline),
            (&["bmi2"], Backend::Baseline),
            (&["adx"], Backend::Baseline),
            (&["avx", "avx2"], Backend::Baseline),
            (&["avx", "avx2", "bmi2"], Backend::Baseline),
            (&["avx", "avx2", "adx"], Backend::Baseline),
            (
                &["avx", "avx2", "avx512f", "avx512ifma", "avx512vl"],
                Backend::Baseline,
            ),
            (&["bmi2", "adx"], Backend::Adx),
            (&["avx", "avx2", "bmi2", "adx"], Backend::Adx),
            (
                &[
                    "avx",
                    "avx2",
                    "avx512f",
                    "bmi2",
                    "adx",
                    "avx512ifma",
                    "avx512vl",
                ],
                Backend::Adx,
            ),
        ];
        for &(features, expected) in cases {
            let backend = Backend::select(Features::of(features));
            assert_eq!(backend, expected, "{features:?}");
        }
    }
}
