module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateResult
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest

/-! Restore and test p using the public original entropy prefix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def CandidateTestPStart (p : CandidatePoint) (s : State) : Prop :=
  CandidateContext p.params p.used s ∧ p.params.length ≤ p.params.bytes.length

theorem candidateTestP_ct (v : RoundImpl) : RelCT isa (Two CandidateTestPStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP,
      VG.Impl.Ffdh.Arm.ParameterCandidate.test false v.name v.code, VG.Impl.Ffdh.Arm.ParameterCandidate.result])
    (fun _ _ => True) := by
  have shapeTrace : RelCT isa (Two CandidateTestPStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (fun _ _ => True) :=
    two_map (fun p => (⟨p.params.out, p.params.tape, p.params.bytes.take p.params.length, p.params.bits⟩ : ShapeData))
      (fun _ _ h => h.1.shape_context h.2) shapeP_ct
  have shape : RelCT isa (Two CandidateTestPStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP
      (Two (CandidateTestStart false)) :=
    two_post shapeTrace (fun p _ h => WP.mono (candidateShape_ok h.1 h.2)
      (fun _ ⟨ctx, _, number, _, _⟩ => ⟨ctx, number, p.params.candidate_odd⟩))
  exact shape.seq ((candidateTestResult_ct v false).seq
    ((candidatePhaseResult_ct false).seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
