module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchBranch
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLoopGuards

/-! # Public successor states for the native parameter-search timing proof -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

def searchContinues (p : SearchPoint) : Prop := p.remaining ≠ 0 ∧
  Spec.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 2

instance (p : SearchPoint) : Decidable (searchContinues p) := inferInstanceAs
  (Decidable (p.remaining ≠ 0 ∧ Spec.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 2))

def nextSearchPoint (p : SearchPoint) : SearchPoint :=
  { p with used := p.used + candidateUsed p.inputs p.used, remaining := p.remaining - 1 }

def SearchCTStep (p : SearchPoint) (s : State) : Prop :=
  if searchContinues p then eval .e s = some true ∧ SearchCTL (nextSearchPoint p) s
  else eval .e s = some false

theorem search_ct_step (v : RoundImpl) (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (iteration (candidateCode v)) s (SearchCTStep p) := by
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (remaining_ready p s h) fun u hu => ?_)
  refine WP.seq (WP.mono (branch_ready v p u hu) fun t ht => ?_)
  by_cases hr : p.remaining = 0
  · simp only [SearchBranchResult, hr, ite_true] at ht
    obtain ⟨original, ht⟩ := ht
    refine WP.mono (done_loop_guard ht) fun q ⟨hq, _⟩ => ?_
    simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hr], ite_false]
    exact hq
  · simp only [SearchBranchResult, hr, ite_false] at ht
    obtain ⟨original, ht⟩ := ht
    cases hc : searchCandidate p.inputs p.used with
    | none =>
      simp only [SearchClassified, hc] at ht
      refine WP.mono (done_loop_guard ht) fun q ⟨hq, _⟩ => ?_
      simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hc, Spec.Ffdh.candidateStatus], ite_false]
      exact hq
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | some prime =>
        simp only [SearchClassified, hc] at ht
        refine WP.mono (done_loop_guard ht) fun q ⟨hq, _⟩ => ?_
        simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hc, Spec.Ffdh.candidateStatus], ite_false]
        exact hq
      | none =>
        simp only [SearchClassified, hc] at ht
        refine WP.mono (live_loop_guard ht.1 ht.2) fun q ⟨hq, hlive⟩ => ?_
        simp only [SearchCTStep, show searchContinues p by simp [searchContinues, hr, hc, Spec.Ffdh.candidateStatus], ite_true]
        exact ⟨hq, original, by simpa only [nextSearchPoint, candidateUsed, hc] using hlive⟩

end VG.Proof.Ffdh.X86_64.Generation
