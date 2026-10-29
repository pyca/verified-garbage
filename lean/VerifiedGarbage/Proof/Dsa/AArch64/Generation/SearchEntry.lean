module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityPlan

import VerifiedGarbage.Proof.Framework.Omega
/-! # Build each p-attempt's proof state from the retained search frame -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/Reframe.lean`, which only this module imported.
section

/-! # Reuse the fixed generation layout at the next offset and witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def HashPlan.reframe (p : HashPlan) (W : Nat → BitVec 64) (offset : Nat)
    (h1 : W 1 = p.W 1) (h3 : W 3 = p.W 3) (h4 : W 4 = p.W 4)
    (h2 : W 2 = BitVec.ofNat 64 offset) (hcarry : offset + p.count < 2 ^ 32) : HashPlan :=
  { p with
    W := W
    offset := offset
    seed_slot := h1.trans p.seed_slot
    wrapped_slot := h3.trans p.wrapped_slot
    output_slot := h4.trans p.output_slot
    offset_slot := h2
    carry := hcarry }

def PConstructPlan.reframe (p : PConstructPlan) (W : Nat → BitVec 64) (offset : Nat)
    (h1 : W 1 = p.hash.W 1) (h3 : W 3 = p.hash.W 3) (h4 : W 4 = p.hash.W 4)
    (h5 : W 5 = p.hash.W 5) (h2 : W 2 = BitVec.ofNat 64 offset)
    (h0 : W 0 = VG.Proof.Bignum.off (W 5) shaped) (hcarry : offset + p.hash.count < 2 ^ 32) : PConstructPlan :=
  { p with
    hash := p.hash.reframe W offset h1 h3 h4 h2 hcarry
    base := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.base
    shapedSlot := h0
    shapedOutside := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.shapedOutside
    shapedHash := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.shapedHash
    shapedInput := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.shapedInput
    qHash := by dsimp only [HashPlan.reframe]; simpa only [HashPlan.changed, h5] using p.qHash
    pOutside := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.pOutside
    exponentOutside := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.exponentOutside
    pExponent := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.pExponent
    frameArithmetic := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.frameArithmetic
    hashArithmetic := by dsimp only [HashPlan.reframe]; simpa only [h5] using p.hashArithmetic }

def PPrimalityPlan.reframe (p : PPrimalityPlan) (W : Nat → BitVec 64) (offset : Nat)
    (h1 : W 1 = p.construct.hash.W 1) (h3 : W 3 = p.construct.hash.W 3)
    (h4 : W 4 = p.construct.hash.W 4) (h5 : W 5 = p.construct.hash.W 5)
    (h14 : W 14 = p.construct.hash.W 14) (h15 : W 15 = p.construct.hash.W 15)
    (h2 : W 2 = BitVec.ofNat 64 offset) (h0 : W 0 = VG.Proof.Bignum.off (W 5) shaped)
    (hcarry : offset + p.construct.hash.count < 2 ^ 32) : PPrimalityPlan :=
  { p with
    construct := p.construct.reframe W offset h1 h3 h4 h5 h2 h0 hcarry
    tapePtr := h14.trans p.tapePtr
    tapeLength := h15.trans p.tapeLength
    bufferSeparate := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.bufferSeparate
    bufferOutside := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.bufferOutside
    tapeBuffer := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.tapeBuffer
    framePrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.framePrime
    hashPrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.hashPrime
    pPrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.pPrime
    exponentPrime := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.exponentPrime
    hashStack := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.hashStack
    arenaBound := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.arenaBound
    tapeArena := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.tapeArena
    arenaFrame := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.arenaFrame
    arenaStack := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [h5] using p.arenaStack
    tapeConstruct := by dsimp only [PConstructPlan.reframe, HashPlan.reframe]; simpa only [PConstructPlan.changed, HashPlan.changed, h5] using p.tapeConstruct }

end VG.Proof.Dsa.AArch64.Generation
end

end

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
