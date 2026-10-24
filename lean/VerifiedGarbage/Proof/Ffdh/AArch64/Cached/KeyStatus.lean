module

public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.Power
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega

/-! Range predicates recover the complete reviewed key-status policy on checked domains. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG

theorem bit_decide (p : Prop) [Decidable p] :
 BitVec.ofNat 64 (decide p).toNat=(if p then 1#64 else 0#64) := by
 by_cases h : p
 · rw [decide_eq_true h,ite_eq_left h];rfl
 · rw [decide_eq_false h,ite_eq_right h];rfl

theorem keyStatus_ranges {a : Spec.Ffdh.Parameters} (valid : Spec.Ffdh.parametersValid a=true) (x : Nat) :
 Spec.Ffdh.keyStatus a x=
 if 0<x ∧ x<Spec.Ffdh.scalarBound a then
  if 1<Spec.Rsa.powMod a.g x a.p ∧ Spec.Rsa.powMod a.g x a.p<a.p-1 then 1 else 3
 else 2 := by
 have scalar : Spec.Ffdh.privateValid a x=false ↔ ¬(0<x ∧ x<Spec.Ffdh.scalarBound a) := by
  simp [Spec.Ffdh.privateValid,Spec.Ffdh.scalarBound]
 rw [VG.Proof.Ffdh.KeyScalar.keyStatus_eq valid]
 simp only [scalar,VG.Proof.Bignum.powMod_eq,VG.Proof.Ffdh.publicValid_power valid x]
 by_cases accepted : 0<x ∧ x<Spec.Ffdh.scalarBound a <;> simp [accepted]

theorem keyStatus_scalar_rejected {a : Spec.Ffdh.Parameters} (valid : Spec.Ffdh.parametersValid a=true) (x : Nat) :
 Spec.Ffdh.keyStatus a x=2 ↔ ¬(0<x ∧ x<Spec.Ffdh.scalarBound a) := by
 rw [keyStatus_ranges valid]
 split
 · split <;> simp_all
 · simp_all

theorem keyStatus_success {a : Spec.Ffdh.Parameters} (valid : Spec.Ffdh.parametersValid a=true) (x : Nat) :
 Spec.Ffdh.keyStatus a x=1 ↔ 0<x ∧ x<Spec.Ffdh.scalarBound a ∧
  1<Spec.Rsa.powMod a.g x a.p ∧ Spec.Rsa.powMod a.g x a.p<a.p-1 := by
 rw [keyStatus_ranges valid]
 split
 · split <;> simp_all
 · simp_all
   omega

end VG.Proof.Ffdh.AArch64.Cached
