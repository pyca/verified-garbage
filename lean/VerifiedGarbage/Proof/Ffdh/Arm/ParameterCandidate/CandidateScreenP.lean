module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenMath
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenPair
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateQOdd
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePairMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateLocalFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSieveMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Reject even q before the paired RSA sieve and witness controller. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateScreenP_ok (v : RoundImpl) {s : State} {p : CandidateParams}
    (h : CandidateContext p p.length s) (enough : p.length≤p.bytes.length)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)=p.candidate) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP v.name v.code) s
      (CandidateReturn p (candidateScreenP p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.screenP VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateQOdd_ok h number) ?_)
  rintro u ⟨ctx,flag,memory,rest⟩
  have numberU : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.out) p.length)=p.candidate := by
    rw [memory]
    exact number
  by_cases oddQ : ((p.candidate-1)/2)%2=1
  · refine WP.seq (WP.ite true (by change some u.z=some true; rw [flag,decide_eq_true oddQ]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateScreenPair_ok v ctx enough numberU oddQ) ?_
    intro t returned
    refine WP.block_nil ?_
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (fun _ h => h)
  · refine WP.seq (WP.ite false (by change some u.z=some false; rw [flag,decide_eq_false oddQ]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateRejected_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreenP_even p (by omega)]
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
