import VerifiedGarbage.Proof.Sm4.Rounds
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Bitsliced SM4: bytes, words and blocks

The code loads and stores 64-bit little-endian words of the blocks: byte
`i` of such a word is bit `8 i … 8 i + 7` (`readW64_bit`). A block's word `w`
is its bytes `4 w … 4 w + 3`, the most significant first (`getLsbD_wordAt`),
and the output block's byte `4 w' + i` is byte `i` of the final word
`3 - w'` (`getLsbD_outBlock`).
-/

namespace VG.Proof.Sm4

open VG VG.Spec.Sm4

/-- Bit `8 i + j` of a little-endian word is bit `j` of its byte `i`. -/
theorem readW64_bit (m : Mem) (a : Addr) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (m.readW a 64).getLsbD (8 * i + j) = (m (a + BitVec.ofNat 64 i)).getLsbD j := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
  simp only [show 8 * i + j < 64 by omega, decide_true, Bool.true_and]

theorem wordAt_eq (b : Block) (i k : Nat) :
    (wordAt b i).getLsbD k =
      (b.getD i 0 ++ b.getD (i + 1) 0 ++ b.getD (i + 2) 0 ++ b.getD (i + 3) 0 : BitVec (8 + 8 + 8 + 8)).getLsbD k :=
  rfl

/-- Bit `j` of byte `i` (from the most significant) of the word at `n`. -/
theorem getLsbD_wordAt (b : Block) (n : Nat) {i j : Nat} (hi : i < 4) (hj : j < 8) :
    (wordAt b n).getLsbD (8 * (3 - i) + j) = (b.getD (n + i) 0).getLsbD j := by
  rw [wordAt_eq]
  simp only [BitVec.getLsbD_append]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.lt_irrefl, Nat.add_zero]

/-- Byte `k` of the output block is byte `k mod 4` of the final word `3 - ⌊k / 4⌋`. -/
theorem getLsbD_outBlock (z : Nat → Word) {k j : Nat} (hk : k < 16) (hj : j < 8) :
    ((outBlock z).getD k 0).getLsbD j = (z (3 - k / 4)).getLsbD (8 * (3 - k % 4) + j) := by
  have : (outBlock z).getD k 0 =
      ((#v[z 3, z 2, z 1, z 0] : Vector Word 4).getD (k / 4) 0 >>> (8 * (3 - k % 4))).setWidth 8 := by
    simp [outBlock, Vector.getD, hk]
  rw [this, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  simp only [hj, decide_true, Bool.true_and]
  rw [show 8 * (3 - k % 4) + j = j + 8 * (3 - k % 4) by omega]
  rcases (show k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 ∨ k / 4 = 3 by omega) with h | h | h | h <;>
    rw [h] <;> rfl

theorem getLsbD_outBlock' (z : Nat → Word) {k j : Nat} (hk : k < 16) (hj : j < 8) :
    ((outBlock z)[k]'hk).getLsbD j = (z (3 - k / 4)).getLsbD (8 * (3 - k % 4) + j) := by
  rw [← getLsbD_outBlock z hk hj]
  simp [Vector.getD, hk]

/-- The block at `p`. -/
theorem blockAt_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (blockAt m p).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [blockAt, Vector.getD, hi]

/-- Bit `8 c + j` of round key `i` of a stored schedule is bit `j` of its byte `4 i + c`. -/
theorem getLsbD_scheduleAt (m : Mem) (p : Addr) {i c j : Nat} (hi : i < 32) (hc : c < 4) (hj : j < 8) :
    ((scheduleAt m p)[i]'hi).getLsbD (8 * c + j) = (m (p + BitVec.ofNat 64 (4 * i + c))).getLsbD j := by
  simp only [scheduleAt, Vector.getElem_ofFn, List.range, List.range.loop, List.foldl]
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;>
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp

end VG.Proof.Sm4
