module

public import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Counter blocks added to as bytes

A counter block byte-reversed (`pshufb` with `revMask`) has the counter's
least significant byte in its most significant byte. Adding 4 to that byte
(`paddd` with `beFour`, 4 in the top byte of doubleword 3) gives the block
of `inc₃₂⁴` of the counter, when that byte is less than 252, so that `inc₃₂`
does not carry out of it (`paddd_beFour`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64

open VG.X86_64
open VG.Spec.Gcm (Block inc32)

/-- 4 in the most significant byte of doubleword 3 of a lane. -/
abbrev beFour : BitVec 128 := 0x04000000000000000000000000000000#128

theorem toNat_append' {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem append_add_hi (b c : BitVec 8) (t : BitVec 24) : (b ++ t) + (c ++ 0#24) = (b + c) ++ t := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat_append', toNat_append', toNat_append', BitVec.toNat_add]
  have := b.isLt; have := c.isLt; have := t.isLt
  simp only [BitVec.toNat_zero]
  omega

/-- `inc₃₂` applied `k` times does not carry out of the least significant
byte. -/
theorem repeat_inc32_lo (Y : Block) (k : Nat) (h : (Y.extractLsb' 0 8).toNat + k < 256) :
    Nat.repeat inc32 k Y = Y.extractLsb' 8 120 ++ (Y.extractLsb' 0 8 + BitVec.ofNat 8 k) := by
  have one : (1 : BitVec 32).toNat = 1 := rfl
  have := Y.isLt
  induction k with
  | zero =>
    apply BitVec.eq_of_toNat_eq
    simp only [Nat.repeat, toNat_append', BitVec.toNat_add, BitVec.extractLsb'_toNat,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
    omega
  | succ k ih =>
    rw [Nat.repeat, ih (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [inc32, toNat_append', BitVec.toNat_add, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one, one] at h ⊢
    omega

theorem getLsbD_rev (Y : BitVec 128) {k r : Nat} (hk : k < 16) (hr : r < 8) :
    (XBinOp.eval .pshufb Y revMask).getLsbD (8 * k + r) = Y.getLsbD (8 * (15 - k) + r) := by
  rw [pshufb_rev, getLsbD_ofBytes _ hk hr]
  simp only [byte, BitVec.getLsbD_extractLsb', decide_eq_true hr, Bool.true_and]

/-- The byte-reversed block: the least significant byte on top. -/
theorem rev_split (Y : BitVec 128) :
    XBinOp.eval .pshufb Y revMask =
      Y.extractLsb' 0 8 ++ (XBinOp.eval .pshufb Y revMask).extractLsb' 0 120 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_append]
  by_cases h : i < 120
  · simp only [h, ite_true, BitVec.getLsbD_extractLsb', decide_true, Bool.true_and, Nat.zero_add]
  · simp only [h, ite_false, BitVec.getLsbD_extractLsb', decide_eq_true (by omega : i - 120 < 8),
      Bool.true_and, Nat.zero_add]
    rw [show i = 8 * 15 + (i - 120) by omega, getLsbD_rev Y (by decide) (by omega)]
    exact congrArg _ (by omega)

/-- The byte-reversed block, but for its top byte, depends only on the
other bytes. -/
theorem rev_lo {Y Y' : BitVec 128} (h : Y.extractLsb' 8 120 = Y'.extractLsb' 8 120) :
    (XBinOp.eval .pshufb Y revMask).extractLsb' 0 120 =
      (XBinOp.eval .pshufb Y' revMask).extractLsb' 0 120 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, Nat.zero_add]
  rw [show i = 8 * (i / 8) + i % 8 by omega, getLsbD_rev Y (by omega) (by omega),
    getLsbD_rev Y' (by omega) (by omega)]
  have := congrArg (BitVec.getLsbD · (8 * (15 - i / 8) + i % 8 - 8)) h
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true (by omega : 8 * (15 - i / 8) + i % 8 - 8 < 120),
    Bool.true_and] at this
  rwa [show 8 + (8 * (15 - i / 8) + i % 8 - 8) = 8 * (15 - i / 8) + i % 8 by omega] at this

theorem paddd_split (b : BitVec 8) (T : BitVec 120) :
    XBinOp.eval .paddd (b ++ T) beFour = (b + 4) ++ T := by
  have lo : ∀ (x : BitVec 8) {q : Nat}, q < 3 → dword (x ++ T) q = T.extractLsb' (32 * q) 32 := by
    intro x q hq
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [dword, BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, BitVec.getLsbD_append,
      show 32 * q + i < 120 by omega, ite_true]
  have hi : ∀ (x : BitVec 8), dword (x ++ T) 3 = x ++ T.extractLsb' 96 24 := by
    intro x
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [dword, BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, BitVec.getLsbD_append]
    by_cases h : i < 24
    · simp only [show 32 * 3 + i < 120 by omega, h, ite_true, decide_true, Bool.true_and]
    · simp only [show ¬ 32 * 3 + i < 120 by omega, h, ite_false]
      exact congrArg _ (by omega)
  apply ext_dword <;> rw [dword_paddd _ _ (by decide)]
  · rw [lo b (by decide), lo _ (by decide), show dword beFour 0 = 0 by decide]
    exact BitVec.add_zero _
  · rw [lo b (by decide), lo _ (by decide), show dword beFour 1 = 0 by decide]
    exact BitVec.add_zero _
  · rw [lo b (by decide), lo _ (by decide), show dword beFour 2 = 0 by decide]
    exact BitVec.add_zero _
  · rw [hi, hi, show dword beFour 3 = 4#8 ++ 0#24 by decide, append_add_hi]
    rfl

/-- Four counter blocks on, through the top byte. -/
theorem paddd_beFour (Y : Block) (h : (Y.extractLsb' 0 8).toNat + 4 < 256) :
    XBinOp.eval .paddd (XBinOp.eval .pshufb Y revMask) beFour =
      XBinOp.eval .pshufb (Nat.repeat inc32 4 Y) revMask := by
  have e := repeat_inc32_lo Y 4 h
  have e8 : (Nat.repeat inc32 4 Y).extractLsb' 8 120 = Y.extractLsb' 8 120 := by
    rw [e]; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, BitVec.getLsbD_append,
      show ¬ 8 + i < 8 by omega, ite_false, show 8 + i - 8 = i by omega]
  have e0 : (Nat.repeat inc32 4 Y).extractLsb' 0 8 = Y.extractLsb' 0 8 + 4 := by
    rw [e]; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, ite_true, Nat.zero_add, hi]
    rfl
  rw [rev_split Y, paddd_split, rev_split (Nat.repeat inc32 4 Y), e0, rev_lo e8]

end VG.Proof.Gcm.X86_64
