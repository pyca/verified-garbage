module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenMath
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateHalve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTests
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateLocalFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSieveMath
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Reject even or small-prime-divisible q before invoking the shared native rounds. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateScreenQ_ok (v : RoundImpl) {s : State} {p : CandidateParams}
    (h : CandidateContext p p.length s) (enough : p.length ≤ p.bytes.length)
    (table : TableData p.base p.length s.mem)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.screenQ v.name v.code) s
      (CandidateReturn p (candidateScreenQ p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.screenQ VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateHalve_ok h table number) ?_)
  rintro u ⟨ctx, tableU, numberU, zero, changed, rest⟩
  by_cases even : ((p.candidate - 1) / 2) % 2 = 0
  · refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true even]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateRejected_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    have answer : candidateScreenQ p = candidateRejected p := by
      rw [candidateScreenQ, even_primeShape even]
      rfl
    rw [answer]
    exact returned.trans_pre (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)
  · refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false even]) (by intro h; cases h) ?_)
    intro _
    have odd : ((p.candidate - 1) / 2) % 2 = 1 := by omega
    have large := p.sieve_large.2
    refine WP.seq (WP.mono (candidateSieve_ok ctx tableU (by rw [numberU]; exact large)
      (by rw [numberU]; exact odd)) ?_)
    rintro w ⟨ctxW, _, flag, bytesW, changedW, restW⟩
    rw [numberU] at flag
    have numberW : Spec.Rsa.os2ip (Spec.Rsa.bytesAt w.mem (State.addr p.out) p.length) = (p.candidate - 1) / 2 := by
      rw [bytesW]
      exact numberU
    by_cases prime : Spec.Ffdh.primeShape ((p.candidate - 1) / 2) = true
    · refine WP.seq (WP.ite true (by change some w.z = some true; rw [flag, prime]) ?_ (by intro h; cases h))
      intro _
      refine WP.mono (candidateTests_ok v ctxW enough numberW odd) ?_
      intro t returned
      refine WP.block_nil (WP.block_nil ?_)
      rw [candidateScreenQ, prime]
      exact (returned.trans_pre (candidate_local_frame ctx (by decide) (by decide) changedW) restW (fun _ h => h)).trans_pre
        (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)
    · have composite : Spec.Ffdh.primeShape ((p.candidate - 1) / 2) = false := Bool.eq_false_iff.mpr prime
      refine WP.seq (WP.ite false (by change some w.z = some false; rw [flag, composite]) (by intro h; cases h) ?_)
      intro _
      refine WP.mono (candidateRejected_ok ctxW) ?_
      intro t returned
      refine WP.block_nil (WP.block_nil ?_)
      rw [candidateScreenQ, composite]
      exact (returned.trans_pre (candidate_local_frame ctx (by decide) (by decide) changedW) restW (fun _ h => h)).trans_pre
        (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
