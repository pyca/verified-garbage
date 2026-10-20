module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchIterationCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTStep
import VerifiedGarbage.Proof.Framework.Omega

/-! # Repeated native candidate retries preserve the public timing relation -/

@[expose] public section

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
