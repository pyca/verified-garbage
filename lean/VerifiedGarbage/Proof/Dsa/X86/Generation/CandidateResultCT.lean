module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateTestState
import Mathlib.Tactic.Attr.Core

/-! # The reviewed primality result determines public status and every continuing cursor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

def candidatePublicResult (P : SearchContextPlan) (value used : Nat) : Nat × Nat :=
  if value < 2 ^ (8 * P.geometry.pLen - 1) then (3, used)
  else match Spec.Dsa.probablePrime value (P.witnesses.bytes.drop used) with
    | none => (0, 0)
    | some (accepted, rest) => (if accepted then 1 else 3, P.witnesses.bytes.length - rest.length)

theorem CandidateTestResult.public {P : SearchContextPlan} {value used : Nat} {r : PrimeStepResult} {s : State}
    (R : CandidateTestResult P value used r s) :
    r.status = (candidatePublicResult P value used).1 ∧
      (r.status ≠ 0 → r.used = (candidatePublicResult P value used).2) := by
  have spec := R.spec
  unfold candidatePublicResult
  split
  · rename_i small
    rw [ite_eq_left small] at spec
    exact ⟨spec.1, fun _ => spec.2⟩
  · rename_i full
    rw [ite_eq_right full] at spec
    rw [← spec]
    unfold primeRunResult
    rcases R.status with zero | one | three
    · simp only [zero, ite_true, ne_eq, not_true_eq_false, false_implies, and_self]
    · simp only [one, show ¬ (1 : Nat) = 0 by decide, ite_false, beq_self_eq_true,
        ite_true, List.length_drop, ne_eq, not_false_eq_true, true_implies, true_and]
      have := R.bound
      omega
    · simp only [three, show ¬ (3 : Nat) = 0 by decide, ite_false, show ((3 : Nat) == 1) = false by decide,
        Bool.false_eq_true, List.length_drop, ne_eq, not_false_eq_true, true_implies, true_and]
      have := R.bound
      omega
end VG.Proof.Dsa.X86.Generation
