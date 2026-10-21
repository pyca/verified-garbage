module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFn
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateEntered
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Framework.Omega

/-! The common AAPCS frame preserves the full candidate's public timing policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateFn_ct (v : RoundImpl) : RelCT isa (Two CandidateFnInput)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) (fun _ _ => True) := by
  refine framed_ct (fun _ _ ⟨_, left, right, _⟩ => ⟨by have := left.stackFits; omega, by have := right.stackFits; omega⟩)
    (fun _ _ ⟨_, _, _, sp⟩ => sp) ?_
  refine (candidateEntered_ct v).mono ?_ (fun _ _ h => h)
  rintro a b ⟨s, t, ⟨p, left, right, sp⟩, rfl, rfl⟩
  exact ⟨p, ⟨left.start, left.incoming, left.out, left.width, left.used, left.bits⟩,
    ⟨right.start, right.incoming, right.out, right.width, right.used, right.bits⟩,
    by change s.sp - 56#32 - 72#32 = t.sp - 56#32 - 72#32; rw [sp]⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
