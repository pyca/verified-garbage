module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenMath
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateCount
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenP
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateLocalFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The entire candidate body: shape, residue, two sieves, and q/p Miller–Rabin. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateMain_ok (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code) s (CandidateReturn p (candidateScreen p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.main VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateCount_ok h enough) ?_)
  rintro u ⟨ctxU, changedU, restU⟩
  refine WP.seq (WP.mono (candidateShape_ok ctxU enough) ?_)
  rintro w ⟨ctxW, _, numberW, changedW, restW⟩
  refine WP.seq (WP.mono (candidateResidue_ok ctxW numberW) ?_)
  rintro a ⟨ctxA, flag, memoryA, restA⟩
  have numberA : Spec.Rsa.os2ip (Spec.Rsa.bytesAt a.mem (State.addr p.out) p.length) = p.candidate := by
    rw [memoryA]
    exact numberW
  by_cases shape : Spec.Ffdh.generationShape p.bits p.generator p.candidate = true
  · refine WP.seq (WP.ite true (by change some a.z = some true; rw [flag, shape]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateScreenP_ok v ctxA enough numberA) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreen, shape]
    exact ((returned.trans_pre (by rw [memoryA]; exact Frame.refl _ _) restA (fun _ h => h)).trans_pre
      (changedW.mono (by simp [candidateRegions])) restW (fun _ h => h)).trans_pre
      (candidate_local_frame h (by decide) (by decide) changedU) restU (fun _ h => h)
  · have badShape : Spec.Ffdh.generationShape p.bits p.generator p.candidate = false := Bool.eq_false_iff.mpr shape
    refine WP.seq (WP.ite false (by change some a.z = some false; rw [flag, badShape]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateRejected_ok ctxA) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreen, badShape]
    exact ((returned.trans_pre (by rw [memoryA]; exact Frame.refl _ _) restA (fun _ h => h)).trans_pre
      (changedW.mono (by simp [candidateRegions])) restW (fun _ h => h)).trans_pre
      (candidate_local_frame h (by decide) (by decide) changedU) restU (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
