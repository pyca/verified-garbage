module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchPlan
import VerifiedGarbage.Proof.Framework.Omega

/-! # Build each p-attempt's proof state from the retained search frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def attemptWords (W : Nat → BitVec 64) (offset : Nat) : Nat → BitVec 64 :=
  upd (upd (upd W 0 (VG.Proof.Bignum.off (W 5) shaped)) 2 (BitVec.ofNat 64 offset)) 25 (W 3)

theorem attemptWords_slot (W : Nat → BitVec 64) (offset : Nat) {k : Nat} (hk : k ∈ searchSlots) :
    attemptWords W offset k = W k := by
  simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [attemptWords, upd]

def SearchMemory.attemptPlan {p : SearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : SearchMemory p W s) (offset : Nat) (hc : offset + p.attempt.construct.hash.count < 2 ^ 32) : PPrimalityPlan :=
  p.attempt.reframe (attemptWords W offset) offset
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 1 (by simp [searchSlots])))
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 3 (by simp [searchSlots])))
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 4 (by simp [searchSlots])))
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 5 (by simp [searchSlots])))
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 14 (by simp [searchSlots])))
    ((attemptWords_slot W offset (by simp [searchSlots])).trans (h.slots 15 (by simp [searchSlots])))
    (by simp [attemptWords, upd]) (by simp [attemptWords, upd]) hc

theorem SearchMemory.entry {p : SearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : SearchMemory p W s) (offset : Nat) (hc : offset + p.attempt.construct.hash.count < 2 ^ 32)
    (H : Spec.Mgf1.Hash) : AttemptEntry (h.attemptPlan offset hc).construct H W s := by
  have h5 := h.slots 5 (by simp [searchSlots])
  have h3 := h.slots 3 (by simp [searchSlots])
  have h26 := h.slots 26 (by simp [searchSlots])
  dsimp only [SearchMemory.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe, HashPlan.reframe]
  refine ⟨h.layout, h.rep, rfl, ?_, h.seedRead, h.wrappedWrite, h.hashWrite, h.seed, ?_, h.scratch,
    ?_, ?_, ?_, ?_, ?_⟩
  · apply h.label.congr rfl rfl
    · simp only [attemptWords, upd, ite_true]
      rw [h3, p.attempt.construct.hash.wrapped_slot, h.label.hl]
    · simpa [attemptWords, upd] using h26
  · exact p.seedSeparate _ (by simp [searchWrites])
  · simpa only [attemptWords, upd, ite_false, show ¬ (5 : Nat) = 25 by decide,
      show ¬ (5 : Nat) = 2 by decide, show ¬ (5 : Nat) = 0 by decide, h5] using h.qSource
  · simpa only [attemptWords, upd, ite_false, show ¬ (5 : Nat) = 25 by decide,
      show ¬ (5 : Nat) = 2 by decide, show ¬ (5 : Nat) = 0 by decide, h5] using
      p.qSeparate _ (by simp [searchWrites])
  · simpa [attemptWords, upd, h5] using h.shapedWrite
  · simpa [attemptWords, upd, h5] using h.pWrite
  · simpa [attemptWords, upd, h5] using h.exponentWrite

end VG.Proof.Dsa.AArch64.Generation
