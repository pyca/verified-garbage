module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryAllocated
import VerifiedGarbage.Proof.Framework.Omega

/-! The public ABI establishes every input invariant of the native search. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem entryInitial {s : State} (h : GenerationABI s) :
    EntryState (contextOf h) (allocState 320 s) where
  sp := rfl
  frame := by
    change Covers [⟨generationBase s, frameBytes⟩] (⟨generationBase s, 320⟩ :: s.wr)
    apply Covers.one
    exact ⟨⟨generationBase s, 320⟩, List.mem_cons_self ..,
      by simpa [off] using
        Offset.contains_base (generationBase s) (d := 0) (n := frameBytes) (k := 320) (by decide) (by decide)⟩
  frameTop := by
    change (generationBase s).toNat + frameBytes ≤ 2 ^ 64
    rw [generationBase_toNat h]
    have hl := h.stackLower
    have hb := s.sp.isLt
    unfold frameBytes
    omega
  scratch := by
    have hb := h.scratchBound
    have hn := generation_scratch_size h
    refine ⟨⟨stackArg s 2, 0, (stackArg s 3).toNat * 8, ?_, ?_, ?_, by omega⟩, ?_⟩
    · change _ ∈ _ :: s.wr
      apply List.mem_cons_of_mem
      rw [h.wr]; simp
    · change stackArg s 2 = off (stackArg s 2) 0
      simp [off]
    · change 0 + usedBytes (s.gpr .x2).toNat ≤ _
      omega
    · change (stackArg s 2).toNat + usedBytes (s.gpr .x2).toNat ≤ 2 ^ 64
      omega
  registers := by
    intro slot hs
    simp only [headerSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  incoming := by
    intro slot hs
    simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact congrArg (fun a => s.mem.readW a 64) (generation_incoming_address s 0)
    · exact congrArg (fun a => s.mem.readW a 64) (generation_incoming_address s 1)
    · exact congrArg (fun a => s.mem.readW a 64) (generation_incoming_address s 2)
  incomingRead := by
    intro slot hs
    simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact allocated_incoming_read h 0 (by decide)
    · exact allocated_incoming_read h 1 (by decide)
    · exact allocated_incoming_read h 2 (by decide)
  hashScratch := rfl
  seeds := allocated_tape h _ _ h.seedsBound h.seedsScratch h.stackSeeds (by rw [h.rd]; simp)
  hs := allocated_tape h _ _ h.hsBound h.hsScratch h.stackHs (by rw [h.rd]; simp)
  rand := allocated_tape h _ _ h.randBound h.randScratch h.stackRand (by rw [h.rd]; simp)

end VG.Proof.Dsa.AArch64.Generation
