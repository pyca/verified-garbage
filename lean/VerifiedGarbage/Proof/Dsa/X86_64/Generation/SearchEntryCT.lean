module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchCTState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero

/-! # Enter each p attempt using only the retained public search words -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

private theorem search_attempt_words {p : SearchPublic} {W : Nat → BitVec 64} {s : State}
    (h : SearchMemory p.plan W s) : PPrimalityWords p.attempt.plan (attemptWords W p.offset) := by
  have h1 := h.slots 1 (by simp [searchSlots])
  have h3 := h.slots 3 (by simp [searchSlots])
  have h4 := h.slots 4 (by simp [searchSlots])
  have h5 := h.slots 5 (by simp [searchSlots])
  have h13 := (h.slots 13 (by simp [searchSlots])).trans p.plan.attempt.tapePtr
  have h15 := (h.slots 15 (by simp [searchSlots])).trans p.plan.attempt.tapeLength
  dsimp only [PPrimalityWords, SearchPublic.attempt, SearchPublic.attemptPlan,
    PPrimalityPlan.reframe, PConstructPlan.reframe, HashPlan.reframe]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [attemptWords, upd, h1, h3, h4, h5]
  · simpa [attemptWords, upd] using h13
  · simpa [attemptWords, upd] using h15

theorem searchEntry_ready {n pLen qLen : Nat} (H : Spec.Mgf1.Hash) {p : SearchPublic} {s : State}
    (h : SearchBefore n pLen qLen p s) :
    WP isa (.block Impl.Dsa.X86_64.Generation.pAttemptArgs) s
      (PPrimalityBefore n H pLen qLen p.attempt) := by
  obtain ⟨⟨W, hs, hu⟩, ctrl, frame, wr, ub, hp, hq⟩ := h
  have entry := hs.entry p.offset p.carry H
  have step := attemptEntry_ok entry ctrl.rdi (ctrl.scr.ld (by decide)) ctrl.offset
  refine WP.mono step fun t ⟨state, ff, hk⟩ => ?_
  have words := search_attempt_words (p := p) hs
  refine ⟨⟨attemptWords W p.offset, words, ?_, frame.congr (hk.gpr (by decide)) hk.2.2, ?_⟩,
    hk.2.2.trans wr, ub, ?_, ?_, hp, hq⟩
  · exact state
  · simpa [SearchPublic.attempt, attemptWords, upd] using hu
  · exact source_of_frame hs.tape ff (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact p.plan.tapeSeparate _ (by
        change (⟨p.plan.attempt.construct.hash.F, frameBytes⟩ : Region) ∈ searchWrites p.plan.attempt p.plan.C
        simp [searchWrites])) p.plan.attempt.randMax hk.2.1 hk.2.2
  · refine ⟨?_, by rw [hk.2.1, hk.2.2]; exact hs.tapeCover⟩
    simpa [SearchPublic.attempt, SearchPublic.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe,
      HashPlan.reframe, attemptWords, upd] using hs.arena.congr hk.2.2

end VG.Proof.Dsa.X86_64.Generation
