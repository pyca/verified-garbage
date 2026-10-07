import VerifiedGarbage.Proof.Divstep.Word32Def
import Mathlib.Data.BitVec

/-! # Word-only arithmetic for the 32-bit divstep implementation -/
namespace VG.Proof.Divstep.W32

theorem shl1 (x : BitVec 32) : x <<< 1 = x + x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq, Nat.pow_one]
  congr 1; omega

end VG.Proof.Divstep.W32
