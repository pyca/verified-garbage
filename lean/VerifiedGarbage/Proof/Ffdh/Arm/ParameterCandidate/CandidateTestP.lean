module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTest
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessProgress

/-! Restore p from the original entropy prefix, test it, and return the candidate result. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateTestP_ok (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP,
      VG.Impl.Ffdh.Arm.ParameterCandidate.test false v.name v.code, VG.Impl.Ffdh.Arm.ParameterCandidate.result]) s
      (CandidateReturn p (witnessRemaining (candidatePhase p false) used 0) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateShape_ok h enough) ?_)
  rintro u ⟨ctx, _, number, changed, rest⟩
  refine WP.seq (WP.mono (candidateTest_ok v ctx number p.candidate_odd) ?_)
  rintro w ⟨next, ctxW, _, status, suffix, bytes, changedW, restW⟩
  refine WP.seq (WP.mono (candidateResult_ok ctxW status suffix (by
    intro _ _
    rw [bytes]
    exact number)) ?_)
  intro t returned
  refine WP.block_nil ?_
  have returnedU := returned.trans_pre (candidate_phase_frame changedW) restW (fun _ h => h)
  exact returnedU.trans_pre (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
