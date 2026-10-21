module

import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Subtract
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Words

/-! # Native subtraction through the borrow forms the negation of a 64-bit pair -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowBit
open VG VG.Proof.Mont.X86

theorem neg_pair (lo hi : BitVec 32) :
    (0#32 - hi - (BitVec.ofBool (decide (0 < lo.toNat))).setWidth 32) ++ (0#32 - lo) = -(hi ++ lo) := by
  let borrow := decide (0 < lo.toNat)
  let carry := decide (0 < hi.toNat + borrow.toNat)
  have L := Mod64.sub_rel (0#32) lo
  have H := sbb_rel (0#32) hi borrow
  simp only [BitVec.toNat_zero, Nat.zero_add] at L H
  change (0#32 - lo).toNat + lo.toNat = 2 ^ 32 * borrow.toNat at L
  change (0#32 - hi - (BitVec.ofBool borrow).setWidth 32).toNat + hi.toNat + borrow.toNat =
    2 ^ 32 * carry.toNat at H
  have paired : ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).toNat +
      (hi ++ lo).toNat = 2 ^ 64 * carry.toNat := by
    rw [Gcd64.append_pair, Gcd64.append_pair]
    unfold Mod64.pair
    omega
  have outputBound := ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).isLt
  have inputBound := (hi ++ lo).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_neg]
  change ((0#32 - hi - (BitVec.ofBool borrow).setWidth 32) ++ (0#32 - lo)).toNat = _
  cases C : carry <;> rw [C] at paired <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at paired <;> omega

end VG.Proof.RsaKeyGen.X86.LowBit
