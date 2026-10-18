module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ABI
import VerifiedGarbage.Proof.Framework.Omega

/-! # The nested ABI frames and scratch allocation realize the search geometry -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.Generation.Layout VG.Impl.RsaOaep.AArch64

def generationBase (s : State) : Addr := s.sp - BitVec.ofNat 64 320

theorem generationBase_toNat {s : State} (h : GenerationABI s) :
    (generationBase s).toNat = (s.sp).toNat - 320 := by
  have hl := h.stackLower
  have hb := (s.sp).isLt
  simp only [generationBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem generation_frame_sub (s : State) :
    Region.Sub ⟨generationBase s, frameBytes⟩ (below (s.sp) 336) :=
  Offset.sub_below _ (by decide) (by decide)

theorem generation_stack_sub (s : State) :
    Region.Sub (below (generationBase s) 16) (below (s.sp) 336) := by
  have he : generationBase s - BitVec.ofNat 64 16 = s.sp - BitVec.ofNat 64 336 := by
    simp only [generationBase, BitVec.sub_sub]
    rfl
  change Region.Sub ⟨_, 16⟩ ⟨_, 336⟩
  rw [he]
  simpa using (Offset.sub_base (s.sp - BitVec.ofNat 64 336) (d := 0) (n := 16) (k := 336) (by decide))

theorem generation_scratch_size {s : State} (h : GenerationABI s) :
    usedBytes (s.gpr .x2).toNat ≤ (stackArg s 3).toNat * 8 := by
  have hl := VG.Proof.Dsa.Generation.generation_layout_fits h.lengths
  have hs := h.scratchLength
  omega

theorem generation_scratch_sub {s : State} (h : GenerationABI s) :
    Region.Sub ⟨stackArg s 2, usedBytes (s.gpr .x2).toNat⟩
      ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩ :=
  by simpa using (Offset.sub_base (stackArg s 2) (d := 0) (by simpa using generation_scratch_size h))

def geometryOf {s : State} (h : GenerationABI s) : GenerationGeometry where
  B := stackArg s 2
  F := generationBase s
  pLen := (s.gpr .x2).toNat
  qLen := (s.gpr .x3).toNat
  lengths := h.lengths
  arenaBound := by have hb := h.scratchBound; have hn := generation_scratch_size h; omega
  frameBound := by rw [generationBase_toNat h]; have hb := (s.sp).isLt; unfold frameBytes; omega
  stackSize := by rw [generationBase_toNat h]; have hl := h.stackLower; omega
  frameArena := (h.stackScratch.sub_left (generation_frame_sub s)).sub_right (generation_scratch_sub h)
  stackArena := (h.stackScratch.sub_left (generation_stack_sub s)).sub_right (generation_scratch_sub h)

def tapeOf {s : State} (h : GenerationABI s) (ptr : Addr) (len : BitVec 64)
    (bound : ptr.toNat + len.toNat ≤ 2 ^ 64)
    (arena : (⟨ptr, len.toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩)
    (stack : (below (s.sp) 336).Disjoint ⟨ptr, len.toNat⟩) : GenerationTape (geometryOf h) where
  ptr := ptr
  bytes := Spec.Rsa.bytesAt s.mem ptr len.toNat
  bound := by rw [bytesAt_length]; exact bound
  size := by rw [bytesAt_length]; exact len.isLt
  arena := by rw [bytesAt_length]; exact arena.sub_right (generation_scratch_sub h)
  frame := by rw [bytesAt_length]; exact (stack.sub_left (generation_frame_sub s)).symm
  stack := by rw [bytesAt_length]; exact (stack.sub_left (generation_stack_sub s)).symm

end VG.Proof.Dsa.AArch64.Generation
