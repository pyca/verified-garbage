module

public import VerifiedGarbage.Spec.RsaKeyGen

/-! # Selecting the unborrowed difference computes the required absolute value -/

@[expose] public section
namespace VG.Proof.RsaKeyGen

theorem absDiff_select {c p d e r : Nat} {borrow reverse : Bool}
    (forward : d + p = c + r * borrow.toNat)
    (backward : e + c = p + r * reverse.toNat)
    (dBound : d < r) (eBound : e < r) :
    (if borrow then e else d) = Spec.RsaKeyGen.absDiff c p := by
  cases borrow <;> cases reverse <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero,
      Bool.false_eq_true, ↓reduceIte] at forward backward ⊢ <;>
    unfold Spec.RsaKeyGen.absDiff <;> split <;> omega

end VG.Proof.RsaKeyGen
