module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseReturnCT

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestPCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrimeCheckCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LeavePhase
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseReturnCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestPCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrimeCheckCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of q's trial division and the witnesses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.RsaKeyGen.X86_64

/-- q is odd: it passed its trial division. -/
def QOdd (p : CandidateP) : Prop := p.Q % 2 = 1

theorem testQ_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two fun d s => OuterState d s ∧ QOdd d.p) (testQ M.mm R.code K.run) fun _ _ => True := by
  unfold testQ
  refine phaseTest_ct M R K true .all QOdd (fun _ _ _ h => h) ?_
    (two_map (fun d : CandidatePublic => d) (fun _ _ h => h.1) (testP_ct M R K))
  refine RelCT.seq (R := Two fun d s => OuterValue false d s ∧ QOdd d.p) (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) shapeOriginal_ct)
    (fun d s h => WP.mono (shape_outer d s h.1) fun _ ht => ⟨ht, h.2⟩)) ?_
  exact two_post (two_map CandidatePublic.outer (fun _ _ h => h.1.1.header) halveOutput_ct)
    (fun d s h => WP.mono (halve_outer d s h.1) fun _ ht => ⟨ht, h.2⟩)

theorem testFirst_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two fun d s => OuterState d s ∧ QOdd d.p) (testFirst M.mm R.code K.run) fun _ _ => True := by
  unfold testFirst
  refine phaseTest_ct M R K false .first QOdd
    (fun d _ h _ => (VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := d.p.bits)
      (by omega_using [h.1.1.1.base.bits1]) _).1) ?_ (testQ_ct M R K)
  exact two_post (two_map CandidatePublic.outer (fun _ _ h => h.1.header) shapeOriginal_ct)
    (fun d s h => WP.mono (shape_outer d s h.1) fun _ ht => ⟨ht, h.2⟩)

private theorem p_leave (d : CandidatePublic) (s : State)
    (h : (PhaseChecked false .all d s ∧ QOdd d.p) ∧ isa.eval .e s = some true) :
    WP isa (.block [VG.Impl.Rsa.X86_64.Crt.leave]) s (fun t => OuterState d t ∧ QOdd d.p) := by
  obtain ⟨_, hg, hp, _⟩ := h.1.1.1.2
  exact WP.mono (leavePhase_ok h.1.1.1.1.1 hg.rdi hp.link)
    fun _ ⟨ht, hd, _, _, _, k⟩ => ⟨⟨⟨ht, k.2.2.trans h.1.1.1.1.2.1, h.1.1.1.1.2.2⟩, hd⟩, h.1.2⟩

/-- p's whole trial division, once q has passed its own. -/
theorem sieveP_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two fun d s => OuterState d s ∧ QOdd d.p) (sieveP M.mm R.code K.run) fun _ _ => True := by
  unfold sieveP
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (R := Two fun d s => OuterValue false d s ∧ QOdd d.p)
    (two_post (two_map CandidatePublic.outer (fun _ _ h => h.1.header) shapeOriginal_ct)
    (fun d s h => WP.mono (shape_outer d s h.1) fun _ ht => ⟨ht, h.2⟩)) ?_
  refine RelCT.seq (R := Two fun d s => PhaseSet false .all d s ∧ QOdd d.p) (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.1.header) (phaseSetup_ct false .all))
    (fun d s h => WP.mono (setup_phase false .all d s h.1) fun _ ht => ⟨ht, h.2⟩)) ?_
  refine RelCT.seq (R := Two fun d s => PhaseLoaded false .all d s ∧ QOdd d.p)
    (two_post (two_map (fun d : CandidatePublic => d) (fun _ _ h => h.1) (loadOutput_ct false .all))
    (fun d s h => WP.mono (load_phase false .all d s h.1) fun _ ht => ⟨ht, h.2⟩)) ?_
  refine RelCT.seq (R := Two fun d s => PhaseChecked false .all d s ∧ QOdd d.p)
    (two_post (two_map (fun d : CandidatePublic => d) (fun _ _ h => h.1) (primeCheck_ct false .all))
    (fun d s h => WP.mono (prime_checked false .all d s h.1) fun _ ht => ⟨ht, h.2⟩)) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.1.2, h₂.1.2]) ?_ ?_
  · exact RelCT.seq (two_post
      (two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.1.link) leave_ct)
      p_leave) (testFirst_ct M R K)
  · exact two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic))
      (fun _ _ h => h.1.1.1.link) innerReject_ct

private theorem q_leave (d : CandidatePublic) (s : State)
    (h : PhaseChecked true .all d s ∧ isa.eval .e s = some true) :
    WP isa (.block [VG.Impl.Rsa.X86_64.Crt.leave]) s (fun t => OuterState d t ∧ QOdd d.p) := by
  have hs : d.p.sieved (d.p.phaseValue true) = true := by
    simpa only [eval, h.1.2, Option.some.injEq] using h.2
  obtain ⟨_, hg, hp, _⟩ := h.1.1.2
  exact WP.mono (leavePhase_ok h.1.1.1.1 hg.rdi hp.link)
    fun _ ⟨ht, hd, _, _, _, k⟩ => ⟨⟨⟨ht, k.2.2.trans h.1.1.1.2.1, h.1.1.1.2.2⟩, hd⟩, odd_of_sieved hs⟩

theorem sieveQ_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two (OuterValue false)) (sieveQ M.mm R.code K.run) fun _ _ => True := by
  unfold sieveQ
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) halveOutput_ct) halve_outer) ?_
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) (phaseSetup_ct true .all)) (setup_phase true .all)) ?_
  refine RelCT.seq (two_post (loadOutput_ct true .all) (load_phase true .all)) ?_
  refine RelCT.seq (two_post (primeCheck_ct true .all) (prime_checked true .all)) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · exact RelCT.seq (two_post
      (two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.link) leave_ct)
      q_leave) (sieveP_ct M R K)
  · exact two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic))
      (fun _ _ h => h.1.1.link) innerReject_ct

end VG.Proof.Ffdh.X86_64.ParameterCandidate
