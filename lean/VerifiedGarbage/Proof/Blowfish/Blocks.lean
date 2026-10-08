import VerifiedGarbage.Proof.Blowfish.Schedule

/-!
# Blocks and their halves, byte by byte

`decodeWord_byte`: byte `b` (from the least significant) of the big-endian
word at offset `o` of a block is the block's byte `o + 3 - b`;
`encodeBlock_byte`: byte `i` of `encodeBlock xL xR` is byte `3 - i` of xL,
or `7 - i` of xR.
-/

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

theorem decodeWord_byte (blk : Block) (o : Nat) {b : Nat} (hb : b < 4) :
    (decodeWord blk o).extractLsb' (8 * b) 8 = blk.getD (o + (3 - b)) 0 := by
  simp only [decodeWord, List.range, List.range.loop, List.foldl_cons, List.foldl_nil, Nat.add_zero]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) [hi, decide_eq_false, BitVec.getLsbD_of_ge,
      show 16 + i - 8 - 8 = i by omega, show 24 + i - 8 - 8 - 8 = i by omega]

theorem blockAt_getD (m : Mem) (q : Addr) {i : Nat} (hi : i < 8) :
    (blockAt m q).getD i 0 = m (q + BitVec.ofNat 64 i) := by
  rw [blockAt, getD_ofFn _ hi]

theorem shr_setWidth (x : Word) (k : Nat) : (x >>> k).setWidth 8 = x.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem encodeBlock_getD (xL xR : Word) {i : Nat} (hi : i < 8) :
    (encodeBlock xL xR).getD i 0 =
      if i < 4 then xL.extractLsb' (8 * (3 - i)) 8 else xR.extractLsb' (8 * (7 - i)) 8 := by
  rw [encodeBlock, getD_ofFn _ hi]
  simp only [shr_setWidth]

/-- A block in memory is the one whose bytes it holds. -/
theorem blockAt_eq (m : Mem) (q : Addr) (blk : Block) (h : ∀ i < 8, m (q + BitVec.ofNat 64 i) = blk.getD i 0) :
    blockAt m q = blk := by
  apply Vector.ext; intro i hi
  have := h i hi
  rw [← blockAt_getD m q hi] at this
  simp only [Vector.getD, Array.getD, Vector.size_toArray, hi, dite_true] at this
  exact this

end VG.Proof.Blowfish
