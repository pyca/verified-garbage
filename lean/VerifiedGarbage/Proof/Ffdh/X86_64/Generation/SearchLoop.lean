module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchSemantics
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLoopGuards
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassify
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchExhausted
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards

/-! # Total correctness of the complete native parameter-search loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search VG.Proof.Ffdh.X86_64.ParameterCandidate

def SearchInvariant (p : SearchPublic) (original : State) (expected : Spec.Ffdh.ParameterSearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used remaining, n = remaining + 1 ∧ SearchLive p original used remaining s ∧
    expected = searchTail p used remaining

theorem search_iteration (v : RoundImpl) {p : SearchPublic} {original s : State}
    {expected : Spec.Ffdh.ParameterSearchResult} {n : Nat}
    (h : SearchInvariant p original expected n s) :
    WP isa (iteration (candidateCode v)) s fun t =>
      (eval .e t = some false ∧ SearchDone p original expected t) ∨
      (eval .e t = some true ∧ ∃ m < n, SearchInvariant p original expected m t) := by
  obtain ⟨used, remaining, hn, h, hexpected⟩ := h
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (remaining_guard h) fun u ⟨hu, he⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (remaining = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    have hresult : expected = .exhausted used := by rw [hexpected, hz', searchTail_zero]
    refine WP.mono (search_exhausted hu) fun t ht => ?_
    refine WP.mono (done_loop_guard ht) fun q ⟨hq, hdone⟩ => ?_
    exact Or.inl ⟨hq, by rw [hresult]; exact hdone⟩
  · intro hnz
    have hr : 0 < remaining := by omega_using [of_decide_eq_false hnz]
    refine WP.seq (WP.mono (search_candidate_run v hu) fun t ⟨ht, hp⟩ => ?_)
    refine WP.mono (search_classify ht hr hp) fun q hq => ?_
    cases hc : searchCandidate p used with
    | none =>
      simp only [SearchClassified, hc] at hq
      have hresult : expected = shortResult p used remaining := hexpected.trans (searchTail_short hr hc)
      refine WP.mono (done_loop_guard hq) fun z ⟨hz, hd⟩ => ?_
      exact Or.inl ⟨hz, by rw [hresult]; exact hd⟩
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | some prime =>
        simp only [SearchClassified, hc] at hq
        have hresult : expected = .accepted prime (used + (p.c.rand.length - used - rest.length)) :=
          hexpected.trans (searchTail_accept hr hc)
        refine WP.mono (done_loop_guard hq) fun z ⟨hz, hd⟩ => ?_
        exact Or.inl ⟨hz, by rw [hresult]; exact hd⟩
      | none =>
        simp only [SearchClassified, hc] at hq
        refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzlive⟩ => ?_
        refine Or.inr ⟨hz, remaining - 1 + 1, by omega_using [hn, hr], ?_⟩
        exact ⟨used + (p.c.rand.length - used - rest.length), remaining - 1,
          rfl, hzlive, hexpected.trans (searchTail_reject hr hc)⟩

theorem search_loop (v : RoundImpl) {p : SearchPublic} {original s : State}
    {expected : Spec.Ffdh.ParameterSearchResult} {n : Nat}
    (h : SearchInvariant p original expected n s) :
    WP isa (.loop (iteration (candidateCode v)) .e) s (SearchDone p original expected) := by
  exact WP.loop (M := isa) (body := iteration (candidateCode v)) (c := .e)
    (Q := SearchDone p original expected) (SearchInvariant p original expected)
    (fun _ _ h => search_iteration v h) n s h

end VG.Proof.Ffdh.X86_64.Generation
