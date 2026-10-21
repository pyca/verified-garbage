module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ScreenedTestsMath
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateHalve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ScreenedAfterQ
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Reconstruct q after p's early witness without requiring the no-longer-needed sieve table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem screenedQ_ok (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate)
    (odd : ((p.candidate - 1) / 2) % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.screenedQ v.name v.code) s
      (CandidateReturn p (screenedQTests p used) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.screenedQ
  refine WP.seq (WP.mono (candidateHalveValue_ok h number) ?_)
  rintro u ⟨context, value, _, changed, rest⟩
  refine WP.mono (screenedAfterQ_ok v context enough value odd) ?_
  intro t returned
  exact returned.trans_pre (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
