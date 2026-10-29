module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABIContext
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState

import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
/-! # The public ABI establishes the complete native generator entry invariant -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntryInputs.lean`, which only this module imported.
section

/-! # Incoming stack arguments remain readable after both entry allocations -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64

theorem allocated_incoming_read {s u : State} (h : GenerationABI s) (hr : u.rd = s.rd)
    (j : Nat) (hj : j < 6) :
    InRegions ((allocState 296 u).rd ++ (allocState 296 u).wr)
      (off (generationBase s) (352 + 8 * j)) 8 := by
  rw [generation_incoming_address]
  refine ⟨⟨stackArgAddr s 0, 48⟩, List.mem_append_left _ ?_, ?_⟩
  · change _ ∈ u.rd
    rw [hr, h.rd]
    simp
  · simp only [stackArgAddr]
    exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8) (k := 48)
      (by omega) (by omega) (by decide)

theorem allocated_incoming_word {s u : State} (h : GenerationABI s)
    (hf : Frame [⟨savedBase s, 48⟩] s.mem u.mem) (j : Nat) (hj : j < 6) :
    word (allocState 296 u).mem (generationBase s) (352 + 8 * j) = stackArg s j := by
  change u.mem.readW (off (generationBase s) (352 + 8 * j)) 64 = _
  rw [generation_incoming_address]
  change u.mem.readW (stackArgAddr s j) 64 = s.mem.readW (stackArgAddr s j) 64
  apply hf.readW (r := ⟨stackArgAddr s 0, 48⟩)
  · simp only [stackArgAddr]
    exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8) (k := 48)
      (by omega) (by omega) (by decide)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (h.stackArgs.sub_left (saved_frame_sub s)).symm
  · decide

theorem allocated_register {s u : State} (hg : u.gpr = (allocState 48 s).gpr)
    (r : Reg) (hr : r ≠ .rsp) : (allocState 296 u).gpr r = s.gpr r := by
  simp only [allocState, State.setReg]
  simp [hr, hg, allocState, State.setReg]

theorem allocated_frame {s u : State} (hg : u.gpr = (allocState 48 s).gpr) :
    (⟨generationBase s, frameBytes⟩ : Region) ∈ (allocState 296 u).wr := by
  have he := allocated_rsp hg
  change u.gpr .rsp - BitVec.ofNat 64 296 = generationBase s at he
  change _ ∈ ⟨u.gpr .rsp - BitVec.ofNat 64 296, 296⟩ :: u.wr
  rw [he]
  exact List.mem_cons_self ..

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem entryInitial {s u : State} (h : GenerationABI s)
    (hg : u.gpr = (allocState 48 s).gpr) (hr : u.rd = s.rd)
    (hw : u.wr = (allocState 48 s).wr)
    (hf : Frame [⟨savedBase s, 48⟩] s.mem u.mem) :
    EntryState (contextOf h) (allocState 296 u) where
  rsp := allocated_rsp hg
  frame := allocated_frame hg
  frameTop := by
    change (generationBase s).toNat + frameBytes + 8 ≤ 2 ^ 64
    rw [generationBase_toNat h]
    have hb := (s.gpr .rsp).isLt
    have hl := h.stackLower
    unfold frameBytes
    omega
  scratch := by
    have hb := h.scratchBound
    have hn := generation_scratch_size h
    refine ⟨⟨stackArg s 4, 0, (stackArg s 5).toNat * 8, ?_, ?_, ?_, by omega⟩, ?_⟩
    · change _ ∈ _ :: u.wr
      apply List.mem_cons_of_mem
      rw [hw]
      change _ ∈ _ :: s.wr
      apply List.mem_cons_of_mem
      rw [h.wr]; simp
    · simp [contextOf, geometryOf, off]
    · change 0 + usedBytes (s.gpr .rdx).toNat ≤ _
      omega
    · change (stackArg s 4).toNat + usedBytes (s.gpr .rdx).toNat ≤ 2 ^ 64
      omega
  registers := by
    intro slot hs
    simp only [headerSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact allocated_register hg _ (by decide)
  incoming := by
    intro slot hs
    simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact allocated_incoming_word h hf 0 (by decide)
    · exact allocated_incoming_word h hf 1 (by decide)
    · exact allocated_incoming_word h hf 2 (by decide)
    · exact allocated_incoming_word h hf 3 (by decide)
    · exact allocated_incoming_word h hf 4 (by decide)
  incomingRead := by
    intro slot hs
    simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact allocated_incoming_read h hr 0 (by decide)
    · exact allocated_incoming_read h hr 1 (by decide)
    · exact allocated_incoming_read h hr 2 (by decide)
    · exact allocated_incoming_read h hr 3 (by decide)
    · exact allocated_incoming_read h hr 4 (by decide)
  seeds := allocated_tape h hr hf _ _ h.seedsBound h.seedsScratch h.stackSeeds (by rw [h.rd]; simp)
  hs := allocated_tape h hr hf _ _ h.hsBound h.hsScratch h.stackHs (by rw [h.rd]; simp)
  rand := allocated_tape h hr hf _ _ h.randBound h.randScratch h.stackRand (by rw [h.rd]; simp)

end VG.Proof.Dsa.X86_64.Generation
