module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.GeneratorCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.InitialStages
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.GeneratorCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestQCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrimeCheckCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT

/-! # FFDH parameter generation on x86-64: timing of the complete candidate flow -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

theorem candidateFilter_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two (OuterValue false)) (candidateFilter M.mm R.code K.run) fun _ _ => True := by
  unfold candidateFilter
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) (phaseSetup_ct false)) (setup_phase false)) ?_
  refine RelCT.seq (two_post (loadOutput_ct false) load_initial) ?_
  refine RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => d) (fun _ _ h => h.1) generatorPolicy_ct) generator_initial) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · refine RelCT.seq (two_post
      (two_map (fun d : CandidatePublic => d) (fun _ _ h => h.1.1.1) (primeCheck_ct false))
      (fun d s h => prime_initial d s h.1.1)) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
    · exact RelCT.seq (two_post
        (two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.1.link) leave_ct)
        (fun d s h => leave_initial d s h.1.1)) (testQ_ct M R K)
    · exact two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.1.link) innerReject_ct
  · exact two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.1.link) innerReject_ct

private theorem shape_initial (d : CandidatePublic) (s : State) (h : OuterState d s ∧ d.used = 0) :
    WP isa shapeOriginal s (fun t => OuterValue false d t ∧ d.used = 0) :=
  WP.mono (shape_outer d s h.1) fun _ ht => ⟨ht, h.2⟩

theorem testCandidate_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two fun d s => OuterState d s ∧ d.used = 0) (testCandidate M.mm R.code K.run) fun _ _ => True := by
  unfold testCandidate
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) shapeOriginal_ct)
    shape_initial) ?_
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.1.header) consumeCandidate_ct) consume_initial) ?_
  exact two_map CandidatePublic.afterCandidate (fun _ _ h => h) (candidateFilter_ct M R K)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
