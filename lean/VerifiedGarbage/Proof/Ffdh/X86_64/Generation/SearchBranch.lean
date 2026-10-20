module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassify
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchExhausted
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards

/-! # Public control-state transitions for paired native search executions -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

def SearchRemainingGuard (p : SearchPoint) (s : State) : Prop := SearchCTL p s ∧
  eval .e s = some (decide (p.remaining = 0))

def SearchBranchResult (p : SearchPoint) (s : State) : Prop :=
  if p.remaining = 0 then ∃ original, SearchDone p.inputs original (.exhausted p.used) s
  else ∃ original, SearchClassified p.inputs original p.used p.remaining s

theorem remaining_ready (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)]) s
      (SearchRemainingGuard p) := by
  obtain ⟨original, h⟩ := h
  exact WP.mono (remaining_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht⟩, he⟩

theorem candidate_ready (v : RoundImpl) (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (candidateRun (candidateCode v)) s (SearchCandidateCT p) := by
  obtain ⟨original, h⟩ := h
  exact WP.mono (search_candidate_run v h) fun _ ⟨ht, hp⟩ => ⟨original, ht, hp⟩

theorem branch_ready (v : RoundImpl) (p : SearchPoint) (s : State) (h : SearchRemainingGuard p s) :
    WP isa (.ite .e exhausted (.seq (candidateRun (candidateCode v)) classify)) s (SearchBranchResult p) := by
  obtain ⟨⟨original, hl⟩, he⟩ := h
  refine WP.ite (decide (p.remaining = 0)) he ?_ ?_
  · intro hz
    change WP isa exhausted s (fun t => SearchBranchResult p t)
    simp only [SearchBranchResult, of_decide_eq_true hz, ite_true]
    exact WP.mono (search_exhausted hl) fun _ ht => ⟨original, ht⟩
  · intro hnz
    change WP isa (.seq _ _) s (fun t => SearchBranchResult p t)
    simp only [SearchBranchResult, of_decide_eq_false hnz, ite_false]
    refine WP.seq (WP.mono (search_candidate_run v hl) fun t ⟨ht, hp⟩ => ?_)
    exact WP.mono (search_classify ht (by omega_using [of_decide_eq_false hnz]) hp) fun _ hq => ⟨original, hq⟩

theorem branch_result_r12 {p : SearchPoint} {s : State} (h : SearchBranchResult p s) :
    s.gpr .r12 = p.inputs.control := by
  by_cases hr : p.remaining = 0
  · simp only [SearchBranchResult, hr, ite_true] at h
    obtain ⟨_, h⟩ := h
    exact h.r12
  · simp only [SearchBranchResult, hr, ite_false] at h
    obtain ⟨original, h⟩ := h
    cases hc : searchCandidate p.inputs p.used with
    | none => simp only [SearchClassified, hc] at h; exact h.r12
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | none => simp only [SearchClassified, hc] at h; exact h.1.r12
      | some prime => simp only [SearchClassified, hc] at h; exact h.r12

end VG.Proof.Ffdh.X86_64.Generation
