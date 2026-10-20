module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geometry
import VerifiedGarbage.Proof.Framework.Offset

/-! # Persistent frame and call stack are disjoint from all arena subregions -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.Mont VG.Impl.Dsa.Generation.Layout

theorem GenerationGeometry.frame_arena (G : GenerationGeometry) :
    (⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint ⟨G.base, usedBytes G.pLen⟩ := by
  have arena := G.arenaBound
  have frame := G.frameBound
  rcases G.separated with before | after
  · apply Offset.disjoint_of_le
    · change G.frameBase.toNat + VG.Impl.Dsa.X86.Generation.frameBytes ≤ G.base.toNat
      rw [G.frame_toNat, G.base_toNat]; exact before
    · change G.base.toNat + usedBytes G.pLen ≤ _
      rw [G.base_toNat]; omega
  · apply Region.Disjoint.symm
    apply Offset.disjoint_of_le
    · change G.base.toNat + usedBytes G.pLen ≤ G.frameBase.toNat
      rw [G.frame_toNat, G.base_toNat]; omega
    · change G.frameBase.toNat + VG.Impl.Dsa.X86.Generation.frameBytes ≤ _
      rw [G.frame_toNat]; omega

theorem GenerationGeometry.frame_part (G : GenerationGeometry) {d n : Nat} (room : d + n ≤ usedBytes G.pLen) :
    (⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint (G.part d n) :=
  G.frame_arena.sub_right (G.part_sub room)

theorem GenerationGeometry.stack_arena (G : GenerationGeometry) :
    (⟨G.frameBase - BitVec.ofNat 64 128, 128⟩ : Region).Disjoint ⟨G.base, usedBytes G.pLen⟩ := by
  have arena := G.arenaBound
  have frame := G.frameBound
  have enough := G.stackSize
  have stack : (G.frameBase - BitVec.ofNat 64 128).toNat = G.frame.toNat - 128 := by
    rw [BitVec.toNat_sub, G.frame_toNat]
    change (2 ^ 64 - 128 + G.frame.toNat) % 2 ^ 64 = G.frame.toNat - 128
    have := G.frame.isLt
    omega
  rcases G.separated with before | after
  · apply Offset.disjoint_of_le
    · change (G.frameBase - BitVec.ofNat 64 128).toNat + 128 ≤ G.base.toNat
      rw [stack, G.base_toNat]; omega
    · change G.base.toNat + usedBytes G.pLen ≤ _
      rw [G.base_toNat]; omega
  · apply Region.Disjoint.symm
    apply Offset.disjoint_of_le
    · change G.base.toNat + usedBytes G.pLen ≤ (G.frameBase - BitVec.ofNat 64 128).toNat
      rw [stack, G.base_toNat]; omega
    · change (G.frameBase - BitVec.ofNat 64 128).toNat + 128 ≤ _
      rw [stack]; have := G.frame.isLt; omega

theorem GenerationGeometry.stack_part (G : GenerationGeometry) {d n : Nat} (room : d + n ≤ usedBytes G.pLen) :
    (⟨G.frameBase - BitVec.ofNat 64 128, 128⟩ : Region).Disjoint (G.part d n) :=
  G.stack_arena.sub_right (G.part_sub room)
end VG.Proof.Dsa.X86.Generation
