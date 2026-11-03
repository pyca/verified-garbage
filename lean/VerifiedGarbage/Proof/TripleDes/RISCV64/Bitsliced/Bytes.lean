module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Blocks as little-endian words

A block's little-endian word holds bit `i` of the block (big-endian, as
`decodeBlock` reads it) at bit `i ^^^ 56`: the byte order is reversed.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.Spec.TripleDes

theorem xor56_eq : ∀ p < 64, p ^^^ 56 = 8 * (7 - p / 8) + p % 8 := by decide

/-- Bit `j` of the little-endian word at `p`: bit `j % 8` of byte `j / 8`. -/
theorem readW_getLsbD (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = (m (p + BitVec.ofNat 64 (j / 8))).getLsbD (j % 8) := by
  rw [← Mem.extractLsb'_read m p (n := 8) (j := j / 8) (by omega), BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.setWidth_eq, show j % 8 < 8 from Nat.mod_lt _ (by decide),
    decide_true, Bool.true_and]
  congr 1; omega

/-- Bit `8 (7 - q) + r` of a block's big-endian word: bit `r` of byte `q`. -/
theorem catBlock_bit (b : Block) {q r : Nat} (hq : q < 8) (hr : r < 8) :
    (VG.Proof.TripleDes.catBlock b).getLsbD (8 * (7 - q) + r) = b[q].getLsbD r := by
  have hcases : ∀ k < 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by decide
  rcases hcases q hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [VG.Proof.TripleDes.catBlock, BitVec.getLsbD_append] <;>
      (repeat' split) <;> first | omega | (congr 1; omega)

/-- The little-endian word of a block, bit by bit. -/
theorem readW_bit (m : Mem) (p : Addr) {j : Nat} (hj : j < 64) :
    (m.readW p 64).getLsbD j = (decodeBlock (blockAt m p)).getLsbD (j ^^^ 56) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, xor56_eq j hj,
    catBlock_bit _ (by omega) (Nat.mod_lt _ (by decide)), readW_getLsbD m p hj]
  simp [blockAt]

/-- A word whose bits are those of `x` at `j ^^^ 56` is the little-endian word of
the block `encodeBlock x`. -/
theorem blockAt_of_readW (m : Mem) (p : Addr) (x : BitVec 64)
    (h : ∀ j < 64, (m.readW p 64).getLsbD j = x.getLsbD (j ^^^ 56)) :
    blockAt m p = encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, encodeBlock, Vector.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  have hj : 8 * i + r < 64 := by omega
  have e := h (8 * i + r) hj
  rw [readW_getLsbD m p hj, xor56_eq _ hj, show (8 * i + r) / 8 = i by omega,
    show (8 * i + r) % 8 = r by omega] at e
  rw [e]
  simp only [BitVec.getLsbD_setWidth, hr, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight]

end VG.Proof.TripleDes.RISCV64.Bitsliced
