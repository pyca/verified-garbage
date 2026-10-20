module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryTape
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers

/-! # The reserved call stack is separate from frame words and public tapes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem GenerationGeometry.frame_below (G : GenerationGeometry) {depth : Nat} (bound : depth ≤ 128) :
    (⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint (below G.frame depth) := by
  change (⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint
    ⟨(G.frame - BitVec.ofNat 32 depth).setWidth 64, depth⟩
  rw [VG.X86.Taint.sub_setWidth (by have := G.stackSize; omega : depth ≤ G.frame.toNat)]
  exact Offset.base_disjoint_below G.frameBase (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; omega)

theorem GenerationTape.below {G : GenerationGeometry} (T : GenerationTape G) {depth : Nat} (bound : depth ≤ 128) :
    (⟨T.pointer.setWidth 64, T.bytes.length⟩ : Region).Disjoint (VG.X86.below G.frame depth) := by
  have separate : (⟨T.pointer.setWidth 64, T.bytes.length⟩ : Region).Disjoint (VG.X86.below G.frame 128) := by
    rw [G.stack_native]
    exact T.stack
  exact separate.sub_right (below_sub bound G.stackSize)
end VG.Proof.Dsa.X86.Generation
