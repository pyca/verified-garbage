module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchSafety
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchEntryCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchFinishCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLoop
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchStart
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchBranch
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLoopGuards
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchIterationCT
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Contract
/-! # Complete native parameter generation has the specified public-tape leakage -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchCTStep.lean`, which only this module imported.
section

/-! # Public successor states for the native parameter-search timing proof -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

def searchContinues (p : SearchPoint) : Prop := p.remaining ≠ 0 ∧
  Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 2

instance (p : SearchPoint) : Decidable (searchContinues p) := inferInstanceAs
  (Decidable (p.remaining ≠ 0 ∧ Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 2))

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
      simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hc, Proof.Ffdh.candidateStatus], ite_false]
      exact hq
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | some prime =>
        simp only [SearchClassified, hc] at ht
        refine WP.mono (done_loop_guard ht) fun q ⟨hq, _⟩ => ?_
        simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hc, Proof.Ffdh.candidateStatus], ite_false]
        exact hq
      | none =>
        simp only [SearchClassified, hc] at ht
        refine WP.mono (live_loop_guard ht.1 ht.2) fun q ⟨hq, hlive⟩ => ?_
        simp only [SearchCTStep, show searchContinues p by simp [searchContinues, hr, hc, Proof.Ffdh.candidateStatus], ite_true]
        exact ⟨hq, original, by simpa only [nextSearchPoint, candidateUsed, hc] using hlive⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchLoopCT.lean`, which only this module imported.
section

/-! # Repeated native candidate retries preserve the public timing relation -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ p, n = p.remaining + 1 ∧ SearchCTL p s ∧ SearchCTL p t

private theorem iteration_pair (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (candidateCode v)) fun s t =>
      eval .e s = eval .e t ∧ (eval .e s = some false → True) ∧
      (eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (p : SearchPoint) (s : State) (h : n = p.remaining + 1 ∧ SearchCTL p s) :
      WP isa (iteration (candidateCode v)) s fun t => n = p.remaining + 1 ∧ SearchCTStep p t :=
    WP.mono (search_ct_step v p s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((search_iteration_ct v).mono
    (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.2, h₂.2⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨p, hn, h₁, h₂⟩ => ⟨p, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨p, ⟨hn, h₁⟩, _, h₂⟩
  by_cases hb : searchContinues p
  · simp only [SearchCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨(nextSearchPoint p).remaining + 1, ?_, nextSearchPoint p, rfl, h₁.2, h₂.2⟩
    dsimp only [nextSearchPoint]
    omega_using [hn, hb.1]
  · simp only [SearchCTStep, hb, ite_false] at h₁ h₂
    refine ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => ?_⟩
    rw [h₁] at ht
    cases ht

theorem search_loop_ct (v : RoundImpl) :
    RelCT isa (Two SearchCTL) (.loop (iteration (candidateCode v)) .e) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨p, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (candidateCode v)) (c := .e)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) (p.remaining + 1)
    _ _ _ _ _ _ ⟨p, rfl, hs, ht⟩ he₁ he₂

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

private def initialPoint (p : SearchPublic) : SearchPoint := ⟨p, 0, p.remaining⟩
private def finalPoint (p : SearchPublic) : SearchEndPoint := ⟨p, searchTail p 0 p.remaining⟩

private theorem entry_started (p : SearchPublic) (s : State) (h : SearchInput p s) :
    WP isa (.block entry) s (SearchCTL (initialPoint p)) :=
  WP.mono (search_start h) fun _ ht => ⟨s, ht⟩

private theorem loop_done (v : RoundImpl) (p : SearchPublic) (s : State) (h : SearchCTL (initialPoint p) s) :
    WP isa (.loop (iteration (candidateCode v)) .e) s (SearchCTDone (finalPoint p)) := by
  obtain ⟨original, h⟩ := h
  have hi : SearchInvariant p original (searchTail p 0 p.remaining) (p.remaining + 1) s :=
    ⟨0, p.remaining, rfl, h, rfl⟩
  exact WP.mono (search_loop v hi) fun _ ht => ⟨original, ht⟩

theorem search_code_ct (v : RoundImpl) :
    RelCT isa (Two SearchInput) (searchCode v) (fun _ _ => True) := by
  unfold searchCode code
  change RelCT isa _ (.seq _ (.seq _ _)) _
  exact RelCT.seq (two_post search_entry_ct entry_started)
    (RelCT.seq (two_post (two_map initialPoint (fun _ _ h => h) (search_loop_ct v)) (loop_done v))
      (two_map finalPoint (fun _ _ h => h) search_finish_ct))

private theorem search_public_descriptor {s t : State} (h : searchPub s t) : searchOfState s = searchOfState t := by
  obtain ⟨⟨hsp, hbytes, r0, r1, r2, r3, r4, r5, a0, a1, a2⟩, ac, hw⟩ := h
  have hrand := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hbytes
  have hc : candidateOfState s = candidateOfState t := by
    simp only [candidateOfState, r0, r1, r2, r3, r4, r5, a1, a2, hrand, hsp]
  change [word s.mem (stackArg s 3) 0, word s.mem (stackArg s 3) 8,
    word s.mem (stackArg s 3) 16, word s.mem (stackArg s 3) 24] =
      [word t.mem (stackArg t 3) 0, word t.mem (stackArg t 3) 8,
        word t.mem (stackArg t 3) 16, word t.mem (stackArg t 3) 24] at hw
  have hcounter : s.mem.readW (stackArg s 3) 64 = t.mem.readW (stackArg t 3) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  unfold searchOfState
  congr 1
  exact congrArg BitVec.toNat hcounter

theorem search_constantTime (v : RoundImpl) :
    ConstantTime isa searchContract.pre searchContract.pub (searchCode v) := by
  refine RelCT.constantTime ((search_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨searchOfState s, ⟨hs, rfl⟩, ht, (search_public_descriptor hp).symm⟩

end VG.Proof.Ffdh.X86_64.Generation
