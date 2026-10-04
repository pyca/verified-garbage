import VerifiedGarbage.Proof.CmacTripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.CmacTripleDes.Des
import VerifiedGarbage.Proof.Framework.Bitslice.Table

/-!
# DES on AArch64: the spread words and the tables

`spreadW w` is `w` rotated left by `rot` bits and spread (`xSrc`), and
`spread k` a round key spread. These are the facts about the layout that the
round needs, each checked over the finite index maps: byte `l` of the
S-boxes' index, `spread k ⊕ spreadW r`, is the input of box `boxOf l`, with
its table in the top two bits (`index_byte`); and the tables hold the
S-boxes' outputs at `posOf` (`sTable_bit`).
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.AArch64 VG.Proof.CmacTripleDes

/-- `w` rotated left by `rot` bits and spread. -/
def spreadW (w : BitVec 32) : BitVec 64 :=
  ofBits 64 fun p => xBit p && w.getLsbD ((xSrc p + 32 - rot) % 32)

theorem getLsbD_spreadW (w : BitVec 32) {p : Nat} (hp : p < 64) :
    (spreadW w).getLsbD p = (xBit p && w.getLsbD ((xSrc p + 32 - rot) % 32)) := by
  rw [spreadW, getLsbD_ofBits, decide_eq_true hp, Bool.true_and]

/-- The box whose input byte `l` holds. -/
def boxOf (l : Nat) : Nat := [2, 0, 6, 4, 1, 7, 5, 3].getD l 0

theorem boxOf_laneOf : ∀ i < 8, boxOf (laneOf i) = i := by decide
theorem laneOf_boxOf : ∀ l < 8, laneOf (boxOf l) = l := by decide
theorem laneOf_lt : ∀ i < 8, laneOf i < 8 := by decide
theorem boxOf_lt : ∀ l < 8, boxOf l < 8 := by decide
theorem tableOf_lt : ∀ i < 8, boxTable i < 4 := by decide

/-- Byte `l` of a spread word: the expansion's bits for box `boxOf l`, and
two zero bits. -/
theorem chunk_layout : ∀ l < 8, ∀ t < 8,
    xBit (8 * l + t) = decide (t < 6) ∧
      (t < 6 → (xSrc (8 * l + t) + 32 - rot) % 32 = expSrc (6 * (7 - boxOf l) + t)) := by
  decide

/-! ## The round keys -/

/-- The round key `k` spread: in byte `laneOf i`, box `i`'s six bits of `k`,
and `boxTable i` in the top two bits (`offsets`). -/
def spread (k : BitVec 64) : BitVec 64 :=
  ofBits 64 fun p =>
    if p % 8 < 6 then k.getLsbD (6 * (7 - boxOf (p / 8)) + p % 8) else offsets.getLsbD p

theorem offsets_bits : ∀ l < 8, ∀ t < 8,
    offsets.getLsbD (8 * l + t) = (decide (6 ≤ t) && (boxTable (boxOf l)).testBit (t - 6)) := by
  decide

theorem getLsbD_spread (k : BitVec 64) {l t : Nat} (hl : l < 8) (ht : t < 8) :
    (spread k).getLsbD (8 * l + t) =
      if t < 6 then k.getLsbD (6 * (7 - boxOf l) + t)
      else (boxTable (boxOf l)).testBit (t - 6) := by
  rw [spread, getLsbD_ofBits, decide_eq_true (by omega), Bool.true_and,
    show (8 * l + t) % 8 = t by omega, show (8 * l + t) / 8 = l by omega]
  split
  · rfl
  · rw [offsets_bits l hl t ht, decide_eq_true (by omega), Bool.true_and]

/-- Byte `l` of the S-boxes' index: box `boxOf l`'s input, after its table. -/
theorem index_byte (k : BitVec 64) (r : BitVec 32) {l : Nat} (hl : l < 8) :
    (spread k ^^^ spreadW r).extractLsb' (8 * l) 8 =
      BitVec.ofNat 8 (2 ^ 6 * boxTable (boxOf l) + (chunk r (k.setWidth 48) (boxOf l)).toNat) := by
  have hb := boxOf_lt l hl
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [BitVec.getLsbD_extractLsb', decide_eq_true ht, Bool.true_and, BitVec.getLsbD_xor,
    getLsbD_spread k hl ht, getLsbD_spreadW r (by omega), BitVec.getLsbD_ofNat,
    decide_eq_true ht, Bool.true_and,
    Nat.testBit_two_pow_mul_add _ (chunk r (k.setWidth 48) (boxOf l)).isLt]
  obtain ⟨hx, he⟩ := chunk_layout l hl t ht
  rw [hx]
  by_cases h6 : t < 6
  · rw [ite_eq_left h6, ite_eq_left h6, he h6, BitVec.testBit_toNat, getLsbD_chunk _ _ hb h6,
      BitVec.getLsbD_setWidth, decide_eq_true (show 6 * (7 - boxOf l) + t < 48 by omega),
      Bool.true_and, decide_eq_true h6, Bool.true_and, Bool.xor_comm]
  · rw [ite_eq_right h6, ite_eq_right h6, decide_eq_false h6, Bool.false_and, Bool.xor_false]

/-! ## The tables -/

theorem sTable_bit : ∀ i < 8, ∀ x < 64, ∀ q < 4,
    (sTable (2 ^ 6 * boxTable i + x)).getLsbD (posOf i q) =
      (Spec.TripleDes.sBox i (BitVec.ofNat 6 x)).getLsbD q := by
  lit_decide

/-! ## `P` -/

theorem pSrc_lt : ∀ j < 32, pSrc j < 32 := by lit_decide


/-- Bit `p` of the spread `P(S)` is output bit `u % 4` of box `7 − u / 4`,
at its bit of `y`, where `u = pSrc ((xSrc p + 32 − rot) % 32)`. -/
theorem ySrc_eq {p : Nat} (hp : xBit p = true) :
    ySrc p = some (8 * laneOf (7 - pSrc ((xSrc p + 32 - rot) % 32) / 4) +
      posOf (7 - pSrc ((xSrc p + 32 - rot) % 32) / 4) (pSrc ((xSrc p + 32 - rot) % 32) % 4)) := by
  simp [ySrc, hp]

end VG.Proof.CmacTripleDes.AArch64
