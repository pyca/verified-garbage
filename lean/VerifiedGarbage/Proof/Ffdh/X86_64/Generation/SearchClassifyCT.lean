module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShortCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassify
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLeafCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShortCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassify
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLeafCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.Contract

/-! # Candidate classification leaks only its public-tape result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchFirstGuard (p : SearchPoint) (s : State) : Prop := SearchCTL p s ∧
  s.gpr .rax = BitVec.ofNat 64 (Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used)) ∧
  eval .e s = some (decide (Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 1))

def SearchSecondGuard (p : SearchPoint) (s : State) : Prop := SearchCTL p s ∧
  eval .e s = some (decide (Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 2))

private theorem first_guard_ready (p : SearchPoint) (s : State) (h : SearchCandidateCT p s) :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 1)]) s (SearchFirstGuard p) := by
  obtain ⟨original, h, hp⟩ := h
  refine WP.mono (candidate_status_guard s) fun t ⟨⟨he, ha, hm⟩, k⟩ => ?_
  exact ⟨⟨original, h.keep k hm (by decide)⟩, normalized_status hp.1 ha, by rw [hp.1] at he; exact he⟩

private theorem second_guard_ready (p : SearchPoint) (s : State) (h : SearchFirstGuard p s) :
    WP isa (.block [.alu .cmp .rax (.imm 2)]) s (SearchSecondGuard p) := by
  obtain ⟨⟨original, hl⟩, ha, _⟩ := h
  have hb : Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) < 2 ^ 64 := by
    cases hc : searchCandidate p.inputs p.used with
    | none => decide
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value <;> dsimp only [Proof.Ffdh.candidateStatus] <;> decide
  exact WP.mono (second_status_guard ha hb) fun _ ⟨⟨he, hm⟩, k⟩ =>
    ⟨⟨original, hl.keep k hm (by decide)⟩, he⟩

theorem search_classify_ct : RelCT isa (Two SearchCandidateCT) classify (fun _ _ => True) := by
  unfold classify
  refine RelCT.seq (two_piece [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide) first_guard_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm) ?_ ?_
  · exact search_accept_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)
  · refine RelCT.seq (R := Two SearchSecondGuard) ?_ ?_
    · exact (two_piece [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide) second_guard_ready).mono
        (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1, h₂.1⟩) (fun _ _ h => h)
    · refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
      · exact search_reject_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)
      · exact search_short_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.X86_64.Generation
