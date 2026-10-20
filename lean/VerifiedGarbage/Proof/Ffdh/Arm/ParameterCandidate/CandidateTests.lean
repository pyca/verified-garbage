module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTest
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTestsMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTestP
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

/-! Compose the full native q-then-p candidate controller and return path. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateTests_ok (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = (p.candidate - 1) / 2)
    (odd : ((p.candidate - 1) / 2) % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code) s
      (CandidateReturn p (candidateTests p used) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.tests VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateTest_ok v (q := true) h number odd) ?_)
  rintro u ⟨next, ctx, _, status, suffix, _, changed, rest⟩
  let answer := witnessRemaining (candidatePhase p true) used 0
  have bound : witnessResultStatus (witnessRemaining (candidatePhase p true) used 0) ≤ 2 :=
    witnessResultStatus_bound _
  refine WP.seq (WP.mono (cmpStatus_ok _ 1 (by omega) (by decide) status) ?_)
  rintro w ⟨⟨zero, memory⟩, restW⟩
  have ctxW := ctx.after_memory memory restW
  have statusW : w.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus answer) :=
    (restW.gpr .r3 (by simp)).trans status
  by_cases go : witnessResultStatus answer = 1
  · refine WP.seq (WP.ite true (by change some w.z = some true; rw [zero, decide_eq_true go]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateTestP_ok v ctxW enough) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [← candidateTests_go p used next go suffix] at returned
    have returnedU := returned.trans_pre (by rw [memory]; exact Frame.refl _ _) restW (by simp)
    exact returnedU.trans_pre (candidate_phase_frame changed) rest (fun _ h => h)
  · refine WP.seq (WP.ite false (by change some w.z = some false; rw [zero, decide_eq_false go]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateResult_ok ctxW statusW suffix (by
      intro tail accepted
      exact False.elim (go (by rw [accepted]; rfl)))) ?_
    intro t returned
    refine WP.block_nil ?_
    change CandidateReturn p (witnessRemaining (candidatePhase p true) used 0) w t at returned
    rw [← candidateTests_stop p used go] at returned
    have returnedU := returned.trans_pre (by rw [memory]; exact Frame.refl _ _) restW (by simp)
    exact returnedU.trans_pre (candidate_phase_frame changed) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
