module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenMath
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePair
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePairMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ScreenedTests
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateLocalFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSieveMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Initialize the RSA table once and screen both moduli at each prime. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateScreenPair_ok (v : RoundImpl) {s : State} {p : CandidateParams}
    (h : CandidateContext p p.length s) (enough : p.length ≤ p.bytes.length)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate)
    (oddQ : ((p.candidate-1)/2)%2=1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair v.name v.code) s
      (CandidateReturn p (candidateScreenP p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateTable_ok h) ?_)
  rintro u ⟨ctx, table, changed, rest⟩
  have bytes := rsa_bytes_frame (src := State.addr p.out) (k := p.length) changed (by have := p.length_bounds; omega) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact p.outputScratch)
  have numberU : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.out) p.length) = p.candidate := by
    rw [bytes]
    exact number
  refine WP.seq (WP.mono (candidatePair_ok ctx table numberU oddQ) ?_)
  rintro w ⟨ctxW, tableW, flag, bytesW, changedW, restW⟩
  change w.z=candidateShapes p at flag
  have numberW : Spec.Rsa.os2ip (Spec.Rsa.bytesAt w.mem (State.addr p.out) p.length) = p.candidate := by
    rw [bytesW]
    exact numberU
  by_cases prime : candidateShapes p = true
  · refine WP.seq (WP.ite true (by change some w.z = some true; rw [flag, prime]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (screenedTests_ok v ctxW enough oddQ) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreenP_shapes, prime]
    exact (returned.trans_pre (candidate_local_frame ctx (by decide) (by decide) changedW) restW (fun _ h => h)).trans_pre
      (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)
  · have composite : candidateShapes p = false := Bool.eq_false_iff.mpr prime
    refine WP.seq (WP.ite false (by change some w.z = some false; rw [flag, composite]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateRejected_ok ctxW) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreenP_shapes, composite]
    exact (returned.trans_pre (candidate_local_frame ctx (by decide) (by decide) changedW) restW (fun _ h => h)).trans_pre
      (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
