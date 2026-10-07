import VerifiedGarbage.Proof.Framework.Mem

/-!
# A 64-bit word read as two 32-bit halves

A 32-bit target reads a table of 64-bit words (`Abi.constsHeld`) half a word
at a time: the low half at the word's address, the high half four bytes on.
-/

namespace VG.Mem

private theorem byte_of_readW64 {m : Mem} {a : Addr} {v : BitVec 64} (h : m.readW a 64 = v)
    {j : Nat} (hj : j < 8) : m (a + BitVec.ofNat 64 j) = v.extractLsb' (8 * j) 8 := by
  rw [← h, ← extractLsb'_read m a hj]
  rfl

/-- The low half of a 64-bit word. -/
theorem readW_lo32 {m : Mem} {a : Addr} {v : BitVec 64} (h : m.readW a 64 = v) :
    m.readW a 32 = v.setWidth 32 := by
  show (m.read a 4).setWidth 32 = _
  rw [read_eq_of_bytes (n := 4) (v := v.setWidth 32) fun j hj => ?_]
  · exact BitVec.setWidth_eq _
  · rw [byte_of_readW64 h (by omega)]
    ext i hi
    simp only [BitVec.getElem_extractLsb']
    rw [BitVec.getLsbD_setWidth, decide_eq_true (by omega : 8 * j + i < 32), Bool.true_and]

/-- The high half of a 64-bit word. -/
theorem readW_hi32 {m : Mem} {a : Addr} {v : BitVec 64} (h : m.readW a 64 = v) :
    m.readW (a + BitVec.ofNat 64 4) 32 = v.extractLsb' 32 32 := by
  show (m.read (a + BitVec.ofNat 64 4) 4).setWidth 32 = _
  rw [read_eq_of_bytes (n := 4) (v := v.extractLsb' 32 32) fun j hj => ?_]
  · exact BitVec.setWidth_eq _
  · rw [Offset.add_add, byte_of_readW64 h (by omega)]
    ext i hi
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb']
    rw [decide_eq_true (by omega : 8 * j + i < 32), Bool.true_and]
    congr 1
    omega

end VG.Mem
