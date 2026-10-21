module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
import VerifiedGarbage.Proof.Bignum.Math

/-! # Carry, borrow and masked selection reduce the doubled remainder exactly once -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64

def choose (carry borrow : Bool) : Bool := decide (borrow.toNat ≤ carry.toNat)

theorem pair_lt (low high : BitVec 32) : pair low high < 2 ^ 64 := by
  unfold pair
  have := low.isLt
  have := high.isLt
  omega

theorem carry_le_borrow {low difference exponent : Nat} {carry borrow : Bool}
    (exponentBound : exponent < 2 ^ 64)
    (sumBound : low + 2 ^ 64 * carry.toNat < 2 * exponent)
    (sub : difference + exponent = low + 2 ^ 64 * borrow.toNat) : carry.toNat ≤ borrow.toNat := by
  cases carry <;> cases borrow <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at * <;> omega

theorem mask_value (carry borrow : Bool) (bound : carry.toNat ≤ borrow.toNat) :
    ((if carry then BitVec.allOnes 32 else 0) + 0#32 + (BitVec.ofBool borrow).setWidth 32) - 1 =
      if choose carry borrow then BitVec.allOnes 32 else 0 := by
  cases carry <;> cases borrow <;> first | rfl | (simp only [Bool.toNat_false, Bool.toNat_true] at bound; omega)

theorem selected_value {low difference exponent : Nat} {carry borrow : Bool}
    (exponentBound : exponent < 2 ^ 64) (differenceBound : difference < 2 ^ 64)
    (lowBound : low < 2 ^ 64) (sumBound : low + 2 ^ 64 * carry.toNat < 2 * exponent)
    (sub : difference + exponent = low + 2 ^ 64 * borrow.toNat) :
    (if choose carry borrow then difference else low) = (low + 2 ^ 64 * carry.toNat) % exponent := by
  have H := VG.Proof.Bignum.csub_result (Tw1 := 0) exponentBound differenceBound (Bool.toNat_le borrow)
    lowBound (by simpa only [Nat.mul_zero, Nat.add_zero] using sumBound) sub
  simp only [Nat.mul_zero, Nat.add_zero] at H
  by_cases accept : borrow.toNat ≤ carry.toNat
  · rw [choose, decide_eq_true accept]
    rw [ite_eq_right (by omega : ¬ carry.toNat < borrow.toNat)] at H
    exact H
  · rw [choose, decide_eq_false accept]
    rw [ite_eq_left (by omega : carry.toNat < borrow.toNat)] at H
    exact H

end VG.Proof.RsaKeyGen.X86.Mod64
