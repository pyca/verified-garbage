module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABIContext
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInputs
import VerifiedGarbage.Proof.Framework.Omega

/-! # The public ABI establishes the complete native generator entry invariant -/

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
