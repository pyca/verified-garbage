import VerifiedGarbage.Proof.GcmSiv.Words
import VerifiedGarbage.Proof.GcmSiv.Ctr

/-!
# AES-GCM-SIV: blocks as 32-bit words

Untrusted: everything here is checked by Lean. The counterparts, on the
32-bit targets, of the lemmas on 64-bit words of `Proof/GcmSiv/Words.lean`,
`Spec.lean` and `Ctr.lean`: a block is four little-endian 32-bit words
`le4 w₀ ++ … ++ le4 w₃`, and a 64-bit word two (`le8_append`). On them:

* POLYVAL's field element of a block and the bytes of one (`ofBytes_le4`,
  `ofBytes_bytesAt`, `toBytes_append4`);
* GHASH's product with `x` (`hkeyOf_words`) and the top bit of a word
  cleared by two shifts (`shl_shr_one`);
* the tag input, the initial counter block and the lengths block
  (`tagOf_words`, `initialCounter_words`, `le64_words`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.GcmSiv.Words32

open VG
open VG.Proof.Cmac (le4 le8 length_le4 length_le8)

/-- The bytes of a 64-bit word made of two 32-bit words. -/
theorem le8_append (a b : BitVec 32) : le8 (a ++ b) = le4 b ++ le4 a := by
  apply List.ext_getElem (by simp [le8, le4])
  intro i h₁ h₂
  have hi : i < 8 := by simpa [le8] using h₁
  simp only [le8, List.getElem_map, List.getElem_range]
  by_cases h4 : i < 4
  · rw [List.getElem_append_left (by simpa [le4] using h4)]
    simp only [le4, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_append,
      show 8 * i + j < 32 by omega, ↓reduceIte]
  · rw [List.getElem_append_right (by simpa [le4] using h4)]
    simp only [le4, List.getElem_map, List.getElem_range, length_le4]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_append,
      show ¬ (8 * i + j < 32) by omega, ↓reduceIte]
    congr 1
    simp only [List.length_map, List.length_range]
    omega

/-- Four words, regrouped as two 64-bit words. -/
theorem append4 (a b c d : BitVec 32) : (a ++ b) ++ (c ++ d) = a ++ b ++ c ++ d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append]
  rcases (by omega : i < 32 ∨ 32 ≤ i ∧ i < 64 ∨ 64 ≤ i ∧ i < 96 ∨ 96 ≤ i) with h | h | h | h
  · simp only [h, show i < 64 by omega, ↓reduceIte]
  · simp only [show ¬ i < 32 by omega, show i < 64 by omega, show i - 32 < 32 by omega, ↓reduceIte]
  · simp only [show ¬ i < 32 by omega, show ¬ i < 64 by omega, show i - 64 < 32 by omega,
      show ¬ i - 32 < 32 by omega, show i - 32 - 32 < 32 by omega, ↓reduceIte]
    congr 1
  · simp only [show ¬ i < 32 by omega, show ¬ i < 64 by omega, show ¬ i - 64 < 32 by omega,
      show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega, ↓reduceIte]
    congr 1

/-- POLYVAL's field element of a block stored as four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    Spec.GcmSiv.ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = d ++ c ++ b ++ a := by
  rw [List.append_assoc, ← le8_append, ← le8_append, ofBytes_le8, append4]

/-- POLYVAL's field element of 16 bytes in memory: four little-endian loads. -/
theorem ofBytes_bytesAt (m : Mem) (p : Addr) :
    Spec.GcmSiv.ofBytes (Spec.Aes.bytesAt m p 16) =
      m.readW (p + BitVec.ofNat 64 12) 32 ++ m.readW (p + BitVec.ofNat 64 8) 32 ++
        m.readW (p + BitVec.ofNat 64 4) 32 ++ m.readW p 32 := by
  rw [Proof.Cmac.bytesAt_split4, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW, ← Proof.Cmac.le4_readW,
    ← Proof.Cmac.le4_readW, ofBytes_le4]

/-- The bytes of a field element made of four words. -/
theorem toBytes_append4 (a b c d : BitVec 32) :
    Spec.GcmSiv.toBytes (a ++ b ++ c ++ d) = le4 d ++ le4 c ++ le4 b ++ le4 a := by
  rw [← append4, toBytes_append, le8_append, le8_append, ← List.append_assoc]

/-- The mask of a word's lowest bit, subtracted from zero: all ones if it is set. -/
theorem neg_and1 (x : BitVec 32) :
    0#32 - (x &&& 1#32) = if x.getLsbD 0 then BitVec.allOnes 32 else 0#32 := by
  have h : x &&& 1#32 = if x.getLsbD 0 then 1#32 else 0#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have h1 : ∀ i < 32, (1#32).getLsbD i = decide (i = 0) := by decide +kernel
    rw [BitVec.getLsbD_and, h1 i hi]
    by_cases h0 : i = 0
    · subst h0; cases x.getLsbD 0 <;> simp
    · cases x.getLsbD 0 <;> simp [h0, h1 i hi]
  rw [h]; cases x.getLsbD 0 <;> decide

/-- A bit of a word or zero, chosen by `b`. -/
theorem getLsbD_ite {w : Nat} (b : Bool) (x : BitVec w) (i : Nat) :
    (if b then x else 0#w).getLsbD i = (b && x.getLsbD i) := by
  cases b <;> simp

/-- GHASH's product with `x` (`Words.hkeyOf`) as 32-bit operations compute it. -/
theorem hkeyOf_words (w₀ w₁ w₂ w₃ : BitVec 32) :
    ((w₃ >>> 1) ^^^ ((0#32 - (w₀ &&& 1#32)) &&& 0xE1000000#32)) ++ ((w₂ >>> 1) ||| (w₃ <<< 31)) ++
      ((w₁ >>> 1) ||| (w₂ <<< 31)) ++ ((w₀ >>> 1) ||| (w₁ <<< 31)) =
    Words.hkeyOf (w₃ ++ w₂ ++ w₁ ++ w₀) := by
  have hR : ∀ i < 128, Spec.Gcm.R.getLsbD i = (decide (96 ≤ i) && (0xE1000000#32).getLsbD (i - 96)) := by
    decide +kernel
  have h0 : (w₃ ++ w₂ ++ w₁ ++ w₀).getLsbD 0 = w₀.getLsbD 0 := by
    simp only [BitVec.getLsbD_append, Nat.reduceLT, ↓reduceIte]
  have hx : ∀ (b : Bool) (x : Spec.Gcm.Block),
      (if b then (x >>> 1) ^^^ Spec.Gcm.R else x >>> 1) = (x >>> 1) ^^^ (if b then Spec.Gcm.R else 0#128) := by
    intro b x; cases b <;> simp
  have hm : ∀ b : Bool, (if b then BitVec.allOnes 32 else 0#32) &&& 0xE1000000#32 =
      if b then 0xE1000000#32 else 0#32 := by
    intro b; cases b <;> simp
  rw [neg_and1 w₀, Words.hkeyOf, h0, hx, hm]
  generalize w₀.getLsbD 0 = b
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, getLsbD_ite, hR i hi]
  clear hR h0 hx hm
  rcases (by omega : i < 31 ∨ i = 31 ∨ 32 ≤ i ∧ i < 63 ∨ i = 63 ∨ 64 ≤ i ∧ i < 95 ∨ i = 95 ∨
      96 ≤ i ∧ i < 127 ∨ i = 127) with h | rfl | h | rfl | h | rfl | h | rfl <;>
    simp (disch := omega) only [↓reduceIte, decide_true, decide_false, ite_eq_left, ite_eq_right,
      decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
      Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or, Bool.xor_false, Bool.false_xor, Nat.sub_sub,
      Nat.add_sub_assoc, Nat.reduceAdd, Nat.reduceSub]
  all_goals try simp (disch := decide) only [BitVec.getLsbD_of_ge, Bool.false_or]

/-- The top bit of a word cleared by shifting it out and back. -/
theorem shl_shr_one (x : BitVec 32) : (x <<< 1) >>> 1 = x &&& 0x7FFFFFFF#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : ∀ i < 32, (0x7FFFFFFF#32 : BitVec 32).getLsbD i = decide (i < 31) := by decide +kernel
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, hm i hi, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 31
  · simp only [show 1 + i < 32 by omega, decide_true, Bool.true_and, show ¬ (1 + i < 1) by omega,
      decide_false, Bool.not_false, h, Bool.and_true]
    congr 1; omega
  · simp only [show ¬ (1 + i < 32) by omega, decide_false, Bool.false_and, h, Bool.and_false]

/-- A word zero-extended to 64 bits. -/
theorem setWidth_64 (x : BitVec 32) : x.setWidth 64 = 0#32 ++ x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  by_cases h : i < 32
  · simp [h, show i < 64 by omega]
  · simp [h, BitVec.getLsbD_of_ge x i (by omega)]

/-- The tag input of POLYVAL's result stored as four words and the nonce as three. -/
theorem tagOf_words (a b c d n₀ n₁ n₂ : BitVec 32) :
    tagOf (le4 a ++ le4 b ++ le4 c ++ le4 d) (le4 n₀ ++ le4 n₁ ++ le4 n₂) =
      le4 (a ^^^ n₀) ++ le4 (b ^^^ n₁) ++ le4 (c ^^^ n₂) ++ le4 ((d <<< 1) >>> 1) := by
  rw [show le4 a ++ le4 b ++ le4 c ++ le4 d = le8 (b ++ a) ++ le8 (d ++ c) by
      rw [le8_append, le8_append, List.append_assoc],
    show le4 n₀ ++ le4 n₁ = le8 (n₁ ++ n₀) by rw [le8_append], GcmSiv.tagOf_words, setWidth_64,
    BitVec.xor_append, BitVec.xor_append,
    show (0x7FFFFFFFFFFFFFFF#64 : BitVec 64) = 0x7FFFFFFF#32 ++ BitVec.allOnes 32 by decide,
    BitVec.and_append, BitVec.and_allOnes, BitVec.xor_zero, ← shl_shr_one, le8_append, le8_append,
    ← List.append_assoc]

/-- The initial counter block of a tag stored as four words. -/
theorem initialCounter_words (a b c d : BitVec 32) :
    Spec.GcmSiv.initialCounter (le4 a ++ le4 b ++ le4 c ++ le4 d) =
      le4 a ++ le4 b ++ le4 c ++ le4 (d ||| 0x80000000#32) := by
  rw [show le4 a ++ le4 b ++ le4 c ++ le4 d = le8 (b ++ a) ++ le8 (d ++ c) by
      rw [le8_append, le8_append, List.append_assoc],
    GcmSiv.initialCounter_words,
    show (0x8000000000000000#64 : BitVec 64) = 0x80000000#32 ++ 0#32 by decide,
    BitVec.or_append, BitVec.or_zero, le8_append, le8_append, ← List.append_assoc]

/-- `little_endian_uint64(8 x)` of a 32-bit `x`, as two words. -/
theorem le64_words (x : BitVec 32) :
    Spec.GcmSiv.le64 (8 * x.toNat) = le4 (x <<< 3) ++ le4 (x >>> 29) := by
  rw [le64_le8, ← le8_append]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  rw [BitVec.toNat_ofNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _),
    Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega

end VG.Proof.GcmSiv.Words32
