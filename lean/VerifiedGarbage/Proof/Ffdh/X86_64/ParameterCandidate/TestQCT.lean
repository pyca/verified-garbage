module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseReturnCT

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestPCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrimeCheckCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseReturnCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestPCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrimeCheckCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of q followed by p -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.RsaKeyGen.X86_64

def CandidatePublic.afterQ (d : CandidatePublic) : CandidatePublic := { d with
  used := match d.decision true with | none => d.used | some (_, rest) => d.p.rand.length - rest.length }

private theorem status_pass {r : Option (Bool × List Byte)} (h : policyStatus r = 1) :
    ∃ rest, r = some (true, rest) := by
  cases r with
  | none => contradiction
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    cases pass
    · simp [policyStatus] at h
    · exact ⟨rest, rfl⟩

private theorem returned_next (d : CandidatePublic) (s : State)
    (h : PhaseReturned true d s ∧ isa.eval .e s = some true) : OuterState d.afterQ s := by
  have hs : policyStatus (d.decision true) = 1 := of_decide_eq_true (by
    simpa only [eval, h.1.2.2.2, Option.some.injEq] using h.2)
  obtain ⟨rest, he⟩ := status_pass hs
  obtain ⟨n, ht, hd, hr⟩ := h.1.1
  have hrest : rest = d.p.rand.drop (d.used + n) := by
    change (match d.decision true with
      | none => _ | some (pass, r) => _ ∧ r = d.p.rand.drop (d.used + n)) at hr
    rw [he] at hr
    exact hr.2
  have hcount : d.used + n = d.p.rand.length - rest.length := by
    rw [hrest, List.length_drop]
    omega_using [ht.bound]
  refine ⟨⟨?_, h.1.2.1, h.1.2.2.1⟩, hd⟩
  change CandidateTape d.p (match d.decision true with | none => d.used | some (_, r) => d.p.rand.length - r.length) s
  rw [he]
  change CandidateTape d.p (d.p.rand.length - rest.length) s
  rw [← hcount]
  exact ht

theorem PhaseLoaded.link {q : Bool} {d : CandidatePublic} {s : State} (h : PhaseLoaded q d s) :
    LinkHeader ⟨d.p.B, d.wr⟩ s := by
  obtain ⟨_, hg, hp, _⟩ := h.2
  exact ⟨h.1.2.2, hg.rdi, h.1.2.1, fun e he => by
    simp only [List.mem_singleton] at he; subst e; exact hp.link⟩

private theorem q_prime {d : CandidatePublic} {s : State}
    (h : PhaseChecked true d s ∧ isa.eval .e s = some true) : PhasePrime true d s := by
  have hs : Spec.Ffdh.primeShape (d.p.phaseValue true) = true := by
    simpa only [eval, h.1.2, Option.some.injEq] using h.2
  unfold Spec.Ffdh.primeShape at hs
  exact ⟨h.1.1, beq_iff_eq.mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hs).1).2⟩

theorem testQ_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two (OuterValue false)) (testQ M.mm R.code K.run) fun _ _ => True := by
  unfold testQ
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) halveOutput_ct) halve_outer) ?_
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) (phaseSetup_ct true)) (setup_phase true)) ?_
  refine RelCT.seq (two_post (loadOutput_ct true) (load_phase true)) ?_
  refine RelCT.seq (two_post (primeCheck_ct true) (prime_checked true)) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · refine RelCT.seq (two_post
      (two_map (fun d : CandidatePublic => d) (fun _ _ h => q_prime h) (modulusPolicy_ct M R K true))
      (fun d s h => modulusPolicy_done M R K true d s (q_prime h))) ?_
    refine RelCT.seq (leaveReturned_ct true) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2.2.2, h₂.2.2.2]) ?_
      (two_taint [] (pins_nil _) (by taint_decide))
    exact two_map CandidatePublic.afterQ returned_next (testP_ct M R K)
  · exact two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic))
      (fun _ _ h => h.1.1.link) innerReject_ct

end VG.Proof.Ffdh.X86_64.ParameterCandidate
