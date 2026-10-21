module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
import VerifiedGarbage.Proof.Framework.Omega

/-! Split p's unchanged witness policy between an early screen and its final batch. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG

def limitedChecks (first : Bool) (checks : Nat) : Nat := if first then 1 else checks - 1

def limitedPhase (p : CandidateParams) (first : Bool) : WitnessParams :=
  { candidatePhase p false with checks := limitedChecks first (Spec.Ffdh.primeChecks p.bits) }

theorem CandidateParams.limited_bounds (p : CandidateParams) (first : Bool) :
    0 < (limitedPhase p first).checks ∧ (limitedPhase p first).checks ≤ 128 := by
  change 0 < limitedChecks first (Spec.Ffdh.primeChecks p.bits) ∧
    limitedChecks first (Spec.Ffdh.primeChecks p.bits) ≤ 128
  by_cases small : p.bits ≤ 2048 <;> cases first <;> simp [limitedChecks, Spec.Ffdh.primeChecks, small]

end VG.Proof.Ffdh.Arm.ParameterCandidate
