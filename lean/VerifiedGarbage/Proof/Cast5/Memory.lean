import VerifiedGarbage.Spec.Cast5
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5: the memory layouts of the contracts

The subkeys are little-endian 32-bit words (`scheduleAt_getD`); a block's
halves are big-endian words, read by a byte reversal of a little-endian load
(`decodeBlock_blockAt`) and written by one before a little-endian store
(`blockAt_write`).
-/

namespace VG.Proof.Cast5

open VG.Spec.Cast5

/-- A 32-bit little-endian read, byte by byte. -/
theorem readW32 (m : Mem) (a : Addr) :
    m.readW a 32 = (m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a : BitVec 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e1 : a + 1 + 1 = a + 2 := by rw [BitVec.add_assoc]; rfl
  have e3 : a + 2 + 1 = a + 3 := by rw [BitVec.add_assoc]; rfl
  simp only [Mem.readW, Mem.read, BitVec.getLsbD_setWidth, BitVec.getLsbD_append, e1, e3]
  have : i - 8 - 8 - 8 < 8 := by omega
  simp [this, hi]

theorem add_ofNat_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) {i : Nat} (hi : i < n) (d : α) :
    (Vector.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [Vector.getD, Array.getD, hi]

/-- Subkey `i` is the little-endian word at `4 i`. -/
theorem scheduleAt_getD (m : Mem) (p : Addr) {i : Nat} (hi : i < 32) :
    (scheduleAt m p).getD i 0 = m.readW (p + BitVec.ofNat 64 (4 * i)) 32 := by
  rw [scheduleAt, getD_ofFn _ hi, readW32, show (3 : Addr) = BitVec.ofNat 64 3 from rfl,
    show (2 : Addr) = BitVec.ofNat 64 2 from rfl, show (1 : Addr) = BitVec.ofNat 64 1 from rfl,
    add_ofNat_add, add_ofNat_add, add_ofNat_add]

theorem blockAt_get (m : Mem) (p : Addr) {j : Nat} (hj : j < 8) :
    (blockAt m p)[j] = m (p + BitVec.ofNat 64 j) := by
  simp [blockAt]

/-- The halves of the block at `p`: big-endian loads. -/
theorem decodeBlock_blockAt (m : Mem) (p : Addr) :
    decodeBlock (blockAt m p) =
      (byteRev32 (m.readW p 32), byteRev32 (m.readW (p + BitVec.ofNat 64 4) 32)) := by
  rw [byteRev32_readW, byteRev32_readW]
  simp only [decodeBlock, blockAt_get m p (show 0 < 8 by decide), blockAt_get m p (show 1 < 8 by decide),
    blockAt_get m p (show 2 < 8 by decide), blockAt_get m p (show 3 < 8 by decide),
    blockAt_get m p (show 4 < 8 by decide), blockAt_get m p (show 5 < 8 by decide),
    blockAt_get m p (show 6 < 8 by decide), blockAt_get m p (show 7 < 8 by decide)]
  have e (a : Nat) : p + BitVec.ofNat 64 a + 1 = p + BitVec.ofNat 64 (a + 1) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, add_ofNat_add]
  have e1 : p + 1 = p + BitVec.ofNat 64 1 := rfl
  simp only [e1, e, Nat.reduceAdd, BitVec.add_zero]

/-- Byte `j` of a byte-reversed word is byte `3 - j` of the word. -/
theorem byteRev32_byte (x : BitVec 32) {j : Nat} (hj : j < 4) :
    (byteRev32 x).extractLsb' (8 * j) 8 = (x >>> (8 * (3 - j))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    decide_eq_true hi, Bool.true_and, byteRev32, getLsbD_cat4]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and] <;>
    exact congrArg _ (by omega)

/-- Storing the byte-reversed halves `x`, `y` writes the block `(x, y)`. -/
theorem blockAt_write (m : Mem) (p : Addr) (x y : Word) :
    blockAt ((m.writeW p (byteRev32 x)).writeW (p + BitVec.ofNat 64 4) (byteRev32 y)) p =
      encodeBlock (x, y) := by
  apply Vector.ext
  intro j hj
  rw [blockAt_get _ _ hj]
  simp only [encodeBlock, Vector.getElem_ofFn, Mem.writeW, Mem.write]
  have h1 : (p + BitVec.ofNat 64 j - (p + BitVec.ofNat 64 4)).toNat = (j + (2 ^ 64 - 4)) % 2 ^ 64 := by
    rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]
    omega
  have h0 : (p + BitVec.ofNat 64 j - p).toNat = j := by
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h0]
  by_cases h4 : j < 4
  · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h4, Nat.mod_eq_of_lt h4]
    simp only [BitVec.setWidth_eq]
    exact byteRev32_byte x h4
  · rw [ite_eq_left (by omega), ite_eq_right h4, show (j + (2 ^ 64 - 4)) % 2 ^ 64 = j - 4 by omega,
      show j % 4 = j - 4 by omega]
    simp only [BitVec.setWidth_eq]
    exact byteRev32_byte y (by omega)

end VG.Proof.Cast5
