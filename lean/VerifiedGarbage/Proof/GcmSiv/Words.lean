import VerifiedGarbage.Proof.GcmSiv.Spec

/-!
# AES-GCM-SIV: GHASH's key and the tag input, on 64-bit words

Untrusted: everything here is checked by Lean. Lemmas any target's
implementation of AES-GCM-SIV that computes POLYVAL with GHASH uses, apart
from the algebra of `Proof/GcmSiv/Polyval.lean` (which they need not import):

* `hkeyOf h`, GHASH's product of `h` with `x` (`Polyval.mulXG`, which
  `Polyval.mulXG_eq_hkeyOf` relates to it), on the halves of a block
  (`hkeyOf_words`);
* `tagInputG`, the tag input of RFC 8452 §4 with POLYVAL replaced by GHASH
  with the key `hkeyOf h` (equal to it by `Polyval.tagInput_eq_tagInputG`);
* the top bit of a word cleared by two shifts (`shl_shr_one`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.GcmSiv.Words

open VG

/-- GHASH's product of `h` with `x`: a shift to the right, reduced by `R`
when the bit shifted out is set. -/
def hkeyOf (h : Spec.Gcm.Block) : Spec.Gcm.Block :=
  if h.getLsbD 0 then (h >>> 1) ^^^ Spec.Gcm.R else h >>> 1

theorem and1 (x : BitVec 64) : x &&& 1#64 = if x.getLsbD 0 then 1#64 else 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
  cases h : x.getLsbD 0
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_zero]
    simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two] at h
    revert h; cases Nat.mod_two_eq_zero_or_one x.toNat <;> simp_all
  · simp only [↓reduceIte, show (1#64).toNat = 1 from rfl]
    simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two] at h
    revert h; cases Nat.mod_two_eq_zero_or_one x.toNat <;> simp_all

theorem appLo (a b : BitVec 64) {j : Nat} (h : j < 64) : (a ++ b).getLsbD j = b.getLsbD j := by
  rw [BitVec.getLsbD_append]; simp [h]

theorem appHi (a b : BitVec 64) {j : Nat} (h : 64 ≤ j) : (a ++ b).getLsbD j = a.getLsbD (j - 64) := by
  rw [BitVec.getLsbD_append]; simp [show ¬ j < 64 by omega]

/-- `hkeyOf` on the halves of a block, for any words `M` and `C` with the
bits of the carry into the low half and of `R` in the high half. -/
theorem hkeyOf_core (hi lo : BitVec 64) (M C : BitVec 64)
    (hM : ∀ i < 64, M.getLsbD i = (decide (i = 63) && hi.getLsbD 0))
    (hC : ∀ i < 64, C.getLsbD i = (Spec.Gcm.R.getLsbD (i + 64) && lo.getLsbD 0))
    (hR : ∀ i < 64, Spec.Gcm.R.getLsbD i = false) :
    ((hi >>> 1) ^^^ C) ++ ((lo >>> 1) ||| M) = hkeyOf (hi ++ lo) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi128
  unfold hkeyOf; rw [appLo hi lo (by decide)]
  by_cases h64 : i < 64
  · rw [appLo _ _ h64, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, hM i h64]
    by_cases h63 : i = 63
    · subst h63
      have e : lo.getLsbD (1 + 63) = false := BitVec.getLsbD_of_ge lo _ (by decide)
      rw [e]
      cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
        BitVec.getLsbD_ushiftRight, appHi hi lo (show 64 ≤ 1 + 63 by decide), hR 63 (by decide)] <;> simp
    · have e : (hi ++ lo).getLsbD (1 + i) = lo.getLsbD (1 + i) := appLo hi lo (by omega)
      cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
        BitVec.getLsbD_ushiftRight, e, hR i h64, decide_eq_false h63] <;> simp
  · rw [appHi _ _ (by omega), BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, hC (i - 64) (by omega),
      show i - 64 + 64 = i by omega]
    have e : (hi ++ lo).getLsbD (1 + i) = hi.getLsbD (1 + (i - 64)) := by
      rw [appHi hi lo (by omega)]; congr 1; omega
    cases hl : lo.getLsbD 0 <;> simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.getLsbD_xor,
      BitVec.getLsbD_ushiftRight, e] <;> simp

/-- GHASH's product with `x`, as a sequence of 64-bit operations computes it
on the halves of a block. -/
theorem hkeyOf_words (hi lo : BitVec 64) :
    ((hi >>> 1) ^^^ (0xE100000000000000#64 &&& (0#64 - (lo &&& 1#64)))) ++
      ((lo >>> 1) ||| (hi &&& 1#64).rotateRight 1) = hkeyOf (hi ++ lo) := by
  have hR : ∀ i < 64, Spec.Gcm.R.getLsbD i = false := by decide +kernel
  have hR' : ∀ i < 64, (0xE100000000000000#64 : BitVec 64).getLsbD i = Spec.Gcm.R.getLsbD (i + 64) := by
    decide +kernel
  have h1 : ∀ i < 64, (0x8000000000000000#64 : BitVec 64).getLsbD i = decide (i = 63) := by decide +kernel
  refine hkeyOf_core hi lo _ _ (fun i hi64 => ?_) (fun i hi64 => ?_) hR
  · rw [and1 hi]; cases h : hi.getLsbD 0 <;> simp [h1 i hi64]
  · rw [and1 lo]; cases h : lo.getLsbD 0 <;> simp [hR' i hi64]

/-- The top bit of a word cleared by shifting it out and back. -/
theorem shl_shr_one (x : BitVec 64) : (x <<< 1) >>> 1 = x &&& 0x7FFFFFFFFFFFFFFF#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : ∀ i < 64, (0x7FFFFFFFFFFFFFFF#64 : BitVec 64).getLsbD i = decide (i < 63) := by decide +kernel
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, hm i hi, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 63
  · simp only [show 1 + i < 64 by omega, decide_true, Bool.true_and, show ¬ (1 + i < 1) by omega,
      decide_false, Bool.not_false, h, Bool.and_true]
    congr 1; omega
  · simp only [show ¬ (1 + i < 64) by omega, decide_false, Bool.false_and, h, Bool.and_false]

/-- The tag input of RFC 8452 §4 (`Spec.GcmSiv.tagInput`), with POLYVAL
computed as GHASH with the key `hkeyOf` of the authentication key. -/
def tagInputG (authKey nonce pt aad : List Byte) : List Byte :=
  tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.ghashFrom (hkeyOf (Spec.GcmSiv.ofBytes authKey)) 0
    (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 aad ++ Spec.GcmSiv.pad16 pt ++
      (Spec.GcmSiv.le64 (8 * aad.length) ++ Spec.GcmSiv.le64 (8 * pt.length)))))) nonce

end VG.Proof.GcmSiv.Words
