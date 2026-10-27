module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABI
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryTape
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import Mathlib.Tactic.ToDual

/-! # The nested ABI frames and scratch allocation realize the search geometry -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.Generation.Layout VG.Impl.RsaOaep.X86_64

def generationBase (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 344

theorem generationBase_toNat {s : State} (h : GenerationABI s) :
    (generationBase s).toNat = (s.gpr .rsp).toNat - 344 := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  simp only [generationBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem generation_frame_sub (s : State) :
    Region.Sub ⟨generationBase s, frameBytes⟩ (below (s.gpr .rsp) 536) :=
  Offset.sub_below _ (by decide) (by decide)

theorem generation_stack_sub (s : State) :
    Region.Sub (below (generationBase s) 192) (below (s.gpr .rsp) 536) := by
  have he : generationBase s - BitVec.ofNat 64 192 = s.gpr .rsp - BitVec.ofNat 64 536 := by
    simp only [generationBase, BitVec.sub_sub]
    rfl
  change Region.Sub ⟨_, 192⟩ ⟨_, 536⟩
  rw [he]
  simpa using (Offset.sub_base (s.gpr .rsp - BitVec.ofNat 64 536) (d := 0) (n := 192) (k := 536) (by decide))

theorem generation_scratch_size {s : State} (h : GenerationABI s) :
    usedBytes (s.gpr .rdx).toNat ≤ (stackArg s 5).toNat * 8 := by
  have hl := VG.Proof.Dsa.Generation.generation_layout_fits h.lengths
  have hs := h.scratchLength
  omega

theorem generation_scratch_sub {s : State} (h : GenerationABI s) :
    Region.Sub ⟨stackArg s 4, usedBytes (s.gpr .rdx).toNat⟩
      ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ :=
  by simpa using (Offset.sub_base (stackArg s 4) (d := 0) (by simpa using generation_scratch_size h))

def geometryOf {s : State} (h : GenerationABI s) : GenerationGeometry where
  B := stackArg s 4
  F := generationBase s
  pLen := (s.gpr .rdx).toNat
  qLen := (s.gpr .rcx).toNat
  lengths := h.lengths
  arenaBound := by have hb := h.scratchBound; have hn := generation_scratch_size h; omega
  frameBound := by rw [generationBase_toNat h]; have hb := (s.gpr .rsp).isLt; unfold frameBytes; omega
  stackSize := by rw [generationBase_toNat h]; have hl := h.stackLower; omega
  frameArena := (h.stackScratch.sub_left (generation_frame_sub s)).sub_right (generation_scratch_sub h)
  stackArena := (h.stackScratch.sub_left (generation_stack_sub s)).sub_right (generation_scratch_sub h)

def tapeOf {s : State} (h : GenerationABI s) (ptr : Addr) (len : BitVec 64)
    (bound : ptr.toNat + len.toNat ≤ 2 ^ 64)
    (arena : (⟨ptr, len.toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩)
    (stack : (below (s.gpr .rsp) 536).Disjoint ⟨ptr, len.toNat⟩) : GenerationTape (geometryOf h) where
  ptr := ptr
  bytes := Spec.Rsa.bytesAt s.mem ptr len.toNat
  bound := by rw [bytesAt_length]; exact bound
  size := by rw [bytesAt_length]; exact len.isLt
  arena := by rw [bytesAt_length]; exact arena.sub_right (generation_scratch_sub h)
  frame := by rw [bytesAt_length]; exact (stack.sub_left (generation_frame_sub s)).symm
  stack := by rw [bytesAt_length]; exact (stack.sub_left (generation_stack_sub s)).symm

end VG.Proof.Dsa.X86_64.Generation
