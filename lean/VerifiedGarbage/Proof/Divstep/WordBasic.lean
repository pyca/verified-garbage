import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Data.BitVec

/-! Elementary word conversions shared by divstep implementations. -/

namespace VG.Proof.Divstep

theorem ofInt_sub' (a b : Int) : BitVec.ofInt 64 (a - b) = BitVec.ofInt 64 a - BitVec.ofInt 64 b := by
  rw [sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- `G & 1` is `G`'s low bit. -/
theorem and_one_word (x : BitVec 64) : x &&& 1 = if x.toNat % 2 = 1 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  split <;> simp_all

/-- A word's value as an integer, modulo `2^64`. -/
theorem toNat_ofInt64 (X : Int) : (((BitVec.ofInt 64 X).toNat : Nat) : Int) = X % 2 ^ 64 := by
  rw [BitVec.toNat_ofInt]; push_cast; exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

end VG.Proof.Divstep
