module

import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyMain
import VerifiedGarbage.Proof.Ffdh.Arm.PrivateSpec

/-! Status 2 discloses exactly scalar rejection, including for unchecked
parameter encodings; no other secret classification is needed for timing. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem keyStatus_two_iff (a : Spec.Ffdh.Parameters) (x : Nat) :
    Spec.Ffdh.keyStatus a x = 2 ↔ Spec.Ffdh.privateValid a x = false := by
  unfold Spec.Ffdh.keyStatus
  cases valid : Spec.Ffdh.privateValid a x
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.true_eq_false]
    split <;> decide

theorem keyStatus_validity_same (a : Spec.Ffdh.Parameters) (x1 x2 : Nat)
    (status : Spec.Ffdh.keyStatus a x1 = Spec.Ffdh.keyStatus a x2) :
    Spec.Ffdh.privateValid a x1 = true ↔ Spec.Ffdh.privateValid a x2 = true := by
  constructor
  · intro good
    cases other : Spec.Ffdh.privateValid a x2
    · have rejected := (keyStatus_two_iff a x1).mp (status.trans ((keyStatus_two_iff a x2).mpr other))
      rw [good] at rejected
      cases rejected
    · rfl
  · intro good
    cases other : Spec.Ffdh.privateValid a x1
    · have rejected := (keyStatus_two_iff a x2).mp (status.symm.trans ((keyStatus_two_iff a x1).mpr other))
      rw [good] at rejected
      cases rejected
    · rfl

end VG.Proof.Ffdh.Arm
