module
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.TCB.X86_64.Sse

import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.X86_64.Avx

/-!
# ML-KEM on x86-64: the even and odd coefficients of `u16`s

The products of the K-PKE cores take the even and the odd coefficients of a
polynomial of `u16`s as the words of two registers. Of eight words `x` and
eight words `y`, the even ones are the low words of their doublewords
(`pslld` then `psrld` by 16), the odd ones their high words (`psrld` by 16),
each packed back to words with `packssdw` (`de16E`, `de16O`). On AVX2 the
halves of a block meet in each 128-bit lane after `vpermq` with `0xD8`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- The low words of the doublewords of `x`, then those of `y`. -/
def de16E (x y : BitVec 128) : BitVec 128 :=
  XBinOp.eval .packssdw (XShiftOp.eval .psrld (XShiftOp.eval .pslld x 16) 16)
    (XShiftOp.eval .psrld (XShiftOp.eval .pslld y 16) 16)

/-- The high words of the doublewords of `x`, then those of `y`. -/
def de16O (x y : BitVec 128) : BitVec 128 :=
  XBinOp.eval .packssdw (XShiftOp.eval .psrld x 16) (XShiftOp.eval .psrld y 16)

theorem dword_lo16 (x : BitVec 128) {j : Nat} (hj : j < 4) :
    (dword (XShiftOp.eval .psrld (XShiftOp.eval .pslld x 16) 16) j).toNat = (word x (2 * j)).toNat := by
  rw [dword_psrld _ _ (by decide) hj, dword_pslld _ _ (by decide) hj, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, dword_eq_words _ hj]
  have h0 := (word x (2 * j)).isLt
  have h1 := (word x (2 * j + 1)).isLt
  simp only [show BitVec.toNat (16 : BitVec 8) = 16 from rfl, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.reducePow]
  omega

theorem dword_hi16 (x : BitVec 128) {j : Nat} (hj : j < 4) :
    (dword (XShiftOp.eval .psrld x 16) j).toNat = (word x (2 * j + 1)).toNat := by
  rw [dword_psrld _ _ (by decide) hj, BitVec.toNat_ushiftRight, dword_eq_words _ hj]
  have h0 := (word x (2 * j)).isLt
  simp only [show BitVec.toNat (16 : BitVec 8) = 16 from rfl, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

/-- The words of `de16E` and `de16O`: of the sixteen words `c` of `x` and
`y`, the even ones and the odd ones, when every one is below `2¹⁵`. -/
theorem de16_words {x y : BitVec 128} {c : Nat → Nat} (hx : ∀ i < 8, (word x i).toNat = c i)
    (hy : ∀ i < 8, (word y i).toNat = c (8 + i)) (hs : ∀ k < 16, c k < 32768) :
    (∀ e < 8, (word (de16E x y) e).toNat = c (2 * e)) ∧
      (∀ e < 8, (word (de16O x y) e).toNat = c (2 * e + 1)) := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · rw [de16E, word_packssdw_small _ _ he (fun j hj => by rw [dword_lo16 _ hj, hx _ (by omega)]; exact hs _ (by omega))
      (fun j hj => by rw [dword_lo16 _ hj, hy _ (by omega)]; exact hs _ (by omega))]
    split
    · rw [dword_lo16 _ (by omega), hx _ (by omega)]
    · rw [dword_lo16 _ (by omega), hy _ (by omega)]; congr 1; omega
  · rw [de16O, word_packssdw_small _ _ he (fun j hj => by rw [dword_hi16 _ hj, hx _ (by omega)]; exact hs _ (by omega))
      (fun j hj => by rw [dword_hi16 _ hj, hy _ (by omega)]; exact hs _ (by omega))]
    split
    · rw [dword_hi16 _ (by omega), hx _ (by omega)]
    · rw [dword_hi16 _ (by omega), hy _ (by omega)]; congr 1; omega

end VG.Proof.MlKem.X86_64
