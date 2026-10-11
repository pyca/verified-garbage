import VerifiedGarbage.Proof.Idea.Memory

/-!
# IDEA: subkeys read with 32-bit loads

Target-independent facts for 32-bit targets: subkey `k` is the low
half of the 32-bit word at its own offset `2k` of the schedule
(`subkey_lo32`), and the last one the high half of the word at 100
(`subkey_hi32`).
-/

namespace VG.Proof.Idea

open VG

theorem subkey_lo32 (m : Mem) (p : Addr) {k : Nat} (hk : k < 52) :
    (m.readW (p + BitVec.ofNat 64 (2 * k)) 32).setWidth 16 = (Spec.Idea.scheduleAt m p).getD k 0 := by
  have e := word_read32 m (p + BitVec.ofNat 64 (2 * k)) 0 (by decide)
  rw [Nat.mul_zero, BitVec.ushiftRight_zero, BitVec.setWidth_setWidth_of_le _ (by decide)] at e
  rw [e, scheduleAt_getD m p (by omega), Offset.add_ofNat_add_ofNat, Nat.zero_add,
    show BitVec.ofNat 64 (2 * 0) = 0 from rfl]
  exact congrArg (_ ++ ·) (congrArg m (BitVec.add_zero _))

theorem subkey_hi32 (m : Mem) (p : Addr) :
    ((m.readW (p + BitVec.ofNat 64 100) 32) >>> 16).setWidth 16 = (Spec.Idea.scheduleAt m p).getD 51 0 := by
  have e := subkey_read32 m p (k := 25) (h := 1) (by decide) (by decide)
  rw [← e]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := (m.readW (p + BitVec.ofNat 64 (4 * 25)) 32).isLt
  rw [Nat.mod_eq_of_lt (by omega : (m.readW (p + BitVec.ofNat 64 (4 * 25)) 32).toNat < 2 ^ 64)]

end VG.Proof.Idea
