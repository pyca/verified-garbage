module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleBound
import VerifiedGarbage.Proof.Ffdh.Arm.VettedCapPolicy
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedSampleHead
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout

/-! Checked domains give a positive reviewed width and exact masked entropy bounds. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedSample
open VG

theorem generation_positive {a : Spec.Ffdh.Parameters} (valid : Spec.Ffdh.parametersValid a = true) :
    0 < Spec.Ffdh.generationScalarBits a := by
  have scalarPositive : 0 < Spec.Ffdh.scalarBound a := by
    unfold Spec.Ffdh.parametersValid at valid
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
    cases present : a.q with
    | none => simp only [Spec.Ffdh.scalarBound, present, Option.getD_none]; omega
    | some q =>
      have facts := valid.2
      rw [present] at facts
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at facts
      simp only [Spec.Ffdh.scalarBound, present, Option.getD_some]
      omega
  have bitPositive : 0 < Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound a) := by
    unfold Spec.RsaKeyGen.bitLength
    rw [ite_eq_right (Nat.ne_of_gt scalarPositive)]
    omega
  cases recognized : Spec.Ffdh.vettedExponentBits a with
  | none => simpa only [Spec.Ffdh.generationScalarBits, recognized] using bitPositive
  | some n =>
    have positive : 0 < n := by
      rcases vetted_caps recognized with rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [Spec.Ffdh.generationScalarBits, recognized]
    omega

theorem bits_positive {p : Inputs} {s : VG.Arm.State} (h : CachedGenerationContext p s) : 0 < bits p := by
  apply generation_positive
  have valid := h.valid
  unfold Spec.Ffdh.domainValid at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.1

theorem bits_bound (p : Inputs) : bits p ≤ 8192 := by
  have bound := Nat.le_trans (VG.Proof.Ffdh.VettedPolicy.bits_le_bound _) p.scalarBound_bits_fit
  have maxLength := p.maxLength
  change Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom) ≤ _
  omega

theorem layoutBound (p : Inputs) (rb : List Byte) (size : rb.length = p.k) :
    Spec.Rsa.os2ip ((ScalarLayout.vetted p).encode rb) <
      2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom) := by
  rw [ScalarLayout.vetted_value size, Spec.Ffdh.vettedScalarOfOctets]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

end VG.Proof.Ffdh.Arm.CachedSample
