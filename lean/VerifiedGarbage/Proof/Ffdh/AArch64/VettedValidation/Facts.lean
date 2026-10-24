module

import VerifiedGarbage.Proof.Ffdh.VettedValidation.Facts
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable
public import VerifiedGarbage.Impl.Ffdh.VettedGroups
public import VerifiedGarbage.Spec.Ffdh.Contract

/-! The AArch64 cap sentinel is non-default only for an algebraically valid domain. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG
open VG.Impl.Ffdh.AArch64.Cached

theorem policyWidth_valid {gs : List Policy.Group} (members : ∀ g∈gs,g∈Policy.groups)
    {k : Nat} {dom : List Byte} (shape : dom.length=2*k ∨ dom.length=3*k)
    (hit : VG.Proof.Ffdh.AArch64.Cached.policyWidth 4095 k dom gs≠4095) : Spec.Ffdh.domainValid k dom=true := by
  induction gs with
  | nil => exact False.elim (hit rfl)
  | cons g gs ih =>
    unfold VG.Proof.Ffdh.AArch64.Cached.policyWidth at hit
    by_cases same : k=g.len ∧ dom=g.domain.take dom.length
    · exact VG.Proof.Ffdh.VettedValidation.matched_domain_valid (members g (by simp)) shape same
    · rw [ite_eq_right same] at hit
      exact ih (fun a h =>members a (by simp [h])) hit

end VG.Proof.Ffdh.AArch64.VettedValidation
