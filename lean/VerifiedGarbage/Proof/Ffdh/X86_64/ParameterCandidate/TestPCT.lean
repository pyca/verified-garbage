module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicyCT

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseReturnCT
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicyCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseReturnCT
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of the complete p phase -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.RsaKeyGen.X86_64

theorem PhaseLoaded.p_prime {d : CandidatePublic} {s : State} (h : PhaseLoaded false d s) : PhasePrime false d s :=
  ⟨h, (VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := d.p.bits)
    (by omega_using [h.1.1.base.bits1]) _).1⟩

theorem testP_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two OuterState) (testP M.mm R.code K.run) fun _ _ => True := by
  unfold testP
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.header) shapeOriginal_ct) shape_outer) ?_
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) (phaseSetup_ct false)) (setup_phase false)) ?_
  refine RelCT.seq (two_post (loadOutput_ct false) (load_phase false)) ?_
  refine RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => d) (fun _ _ h => h.p_prime) (modulusPolicy_ct M R K false))
    (fun d s h => modulusPolicy_done M R K false d s h.p_prime)) ?_
  refine RelCT.seq (leaveReturned_ct false) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2.2.2, h₂.2.2.2]) ?_
    (two_taint [] (pins_nil _) (by taint_decide))
  exact two_map CandidatePublic.outer (fun _ _ h => h.1.outer) shapeOriginal_ct

end VG.Proof.Ffdh.X86_64.ParameterCandidate
