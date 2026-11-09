module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicyCT

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseReturnCT
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicyCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseReturnCT
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of a witness phase

`phaseTest_ct`: one modulus's witnesses and what follows them leak the same
in runs that agree on the public data; `testP_ct`: p's other witnesses.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.RsaKeyGen.X86_64

/-- The public data after phase `q`: the octets it read. -/
def CandidatePublic.after (d : CandidatePublic) (q : Bool) (c : Checks) : CandidatePublic := { d with
  used := match d.decision q c with | none => d.used | some (_, rest) => d.p.rand.length - rest.length }

private theorem status_pass {r : Option (Bool × List Byte)} (h : policyStatus r = 1) :
    ∃ rest, r = some (true, rest) := by
  cases r with
  | none => contradiction
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    cases pass
    · simp [policyStatus] at h
    · exact ⟨rest, rfl⟩

theorem returned_next {q : Bool} {c : Checks} (d : CandidatePublic) (s : State)
    (h : PhaseReturned q c d s ∧ isa.eval .e s = some true) : OuterState (d.after q c) s := by
  have hs : policyStatus (d.decision q c) = 1 := of_decide_eq_true (by
    simpa only [eval, h.1.2.2.2, Option.some.injEq] using h.2)
  obtain ⟨rest, he⟩ := status_pass hs
  obtain ⟨n, ht, hd, hr⟩ := h.1.1
  have hrest : rest = d.p.rand.drop (d.used + n) := by
    change (match d.decision q c with
      | none => _ | some (pass, r) => _ ∧ r = d.p.rand.drop (d.used + n)) at hr
    rw [he] at hr
    exact hr.2
  have hcount : d.used + n = d.p.rand.length - rest.length := by
    rw [hrest, List.length_drop]
    omega_using [ht.bound]
  refine ⟨⟨?_, h.1.2.1, h.1.2.2.1⟩, hd⟩
  change CandidateTape d.p (match d.decision q c with | none => d.used | some (_, r) => d.p.rand.length - r.length) s
  rw [he]
  change CandidateTape d.p (d.p.rand.length - rest.length) s
  rw [← hcount]
  exact ht

theorem phaseTest_ct (M : Mont) (R : R2Impl M) (K : Kernel) {Φ : CandidatePublic → State → Prop}
    {prep next : Prog isa} (q : Bool) (c : Checks) (I : CandidateP → Prop)
    (hodd : ∀ d s, OuterValue q d s → I d.p → d.p.phaseValue q % 2 = 1)
    (hprep : RelCT isa (Two Φ) prep (Two fun d s => OuterValue q d s ∧ I d.p))
    (hnext : RelCT isa (Two fun d s => OuterState d s ∧ I d.p) next fun _ _ => True) :
    RelCT isa (Two Φ) (phaseTest M.mm R.code K.run prep q c next) fun _ _ => True := by
  unfold phaseTest
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq hprep ?_
  refine RelCT.seq (R := Two fun d s => PhaseSet q c d s ∧ d.p.phaseValue q % 2 = 1 ∧ I d.p) (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.1.header) (phaseSetup_ct q c))
    (fun d s h => WP.mono (setup_phase q c d s h.1) fun _ ht => ⟨ht, hodd d s h.1 h.2, h.2⟩)) ?_
  refine RelCT.seq (R := Two fun d s => PhaseLoaded q c d s ∧ d.p.phaseValue q % 2 = 1 ∧ I d.p) (two_post
    (two_map (fun d : CandidatePublic => d) (fun _ _ h => h.1) (loadOutput_ct q c))
    (fun d s h => WP.mono (load_phase q c d s h.1) fun _ ht => ⟨ht, h.2⟩)) ?_
  refine RelCT.seq (R := Two fun d s => PhaseDone q c d s ∧ I d.p) (two_post
    (two_map (fun d : CandidatePublic => d) (fun _ _ h => ⟨h.1, h.2.1⟩) (modulusPolicy_ct M R K q c))
    (fun d s h => WP.mono (modulusPolicy_done M R K q c d s ⟨h.1, h.2.1⟩) fun _ ht => ⟨ht, h.2.2⟩)) ?_
  refine RelCT.seq (R := Two fun d s => PhaseReturned q c d s ∧ I d.p) (two_post
    (two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.link) leaveStatus_ct)
    (fun d s h => WP.mono (phaseReturned q c d s h.1) fun _ ht => ⟨ht, h.2⟩)) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.1.2.2.2, h₂.1.2.2.2]) ?_
    (two_taint [] (pins_nil _) (by taint_decide))
  exact two_map (fun d : CandidatePublic => d.after q c) (fun d s h => ⟨returned_next d s ⟨h.1.1, h.2⟩, h.1.2⟩) hnext

theorem testP_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two OuterState) (testP M.mm R.code K.run) fun _ _ => True := by
  unfold testP
  refine (phaseTest_ct M R K false .rest (fun _ => True)
    (fun d _ h _ => (VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := d.p.bits)
      (by omega_using [h.1.1.1.base.bits1]) _).1) ?_ ?_)
  · exact two_post (two_map CandidatePublic.outer (fun _ _ h => h.header) shapeOriginal_ct)
      (fun d s h => WP.mono (shape_outer d s h) fun _ ht => ⟨ht, trivial⟩)
  · exact two_map CandidatePublic.outer (fun _ _ h => h.1.header) shapeOriginal_ct

end VG.Proof.Ffdh.X86_64.ParameterCandidate
