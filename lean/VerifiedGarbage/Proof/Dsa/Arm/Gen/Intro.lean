module

import VerifiedGarbage.Proof.Dsa.Arm.Gen.Test
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.St
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
import VerifiedGarbage.Proof.Dsa.Arm.Gen.CT

/-! # DSA parameter generation on ARMv7: a stage's pure facts as hypotheses -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

/-- A stage's pure facts, as hypotheses. -/
theorem VP.intro {P : Prop} {F Q : State → State → Prop} {c : Prog isa} (h : P → VP F c Q) :
    VP (fun σ s => P ∧ F σ s) c Q := by
  by_cases hp : P
  · exact (h hp).mono (fun σ s h => h.2) fun _ _ h => h
  · exact VP.of_false fun σ s h => hp h.1

end VG.Proof.Dsa.Arm.Gen
