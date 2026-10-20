module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryContributions
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryStack

/-! # Every hash contribution preserves the seed, frame, and other digest blocks -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem contributionWrites_sub {H : Hash} (K : HashOK H) (G : GenerationGeometry)
    (T : GenerationTape G) (offset : Nat) (len : T.bytes.length = G.qLen) (final : H.F = G.qLen)
    {j : Nat} (hj : j ≤ G.contributionCount) :
    ∀ r ∈ (G.contributions T offset).writes K j,
      ∃ outer ∈ [⟨G.base, usedBytes G.pLen⟩, below G.frame 48], r.Sub outer := by
  rw [G.contribution_writes K T offset len final hj]
  intro r hr
  have qwidth := G.qWidth
  have stateBound := K.hSB
  have workBound := K.hWb
  have work := K.hW
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨G.base, usedBytes G.pLen⟩, by simp, G.part_sub (by unfold wrappedSeed usedBytes domainCheck; omega)⟩
  · exact ⟨⟨G.base, usedBytes G.pLen⟩, by simp, G.part_sub (by
      unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [stateBound])⟩
  · exact ⟨⟨G.base, usedBytes G.pLen⟩, by simp, G.part_sub (G.contribution_room hj)⟩
  · exact ⟨⟨G.base, usedBytes G.pLen⟩, by simp, G.part_sub (by
      unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [workBound, work])⟩
  · exact ⟨below G.frame 48, by simp, fun _ h => h⟩

theorem contributionLayout {H : Hash} (K : HashOK H) (G : GenerationGeometry)
    (T : GenerationTape G) (offset : Nat) (len : T.bytes.length = G.qLen)
    (digest : H.D = G.qLen) (final : H.F = G.qLen)
    (offsetBound : offset + G.contributionCount < 2 ^ 24) : ContributionLayout K (G.contributions T offset) := by
  have qwidth := G.qWidth
  have qpos : 0 < G.qLen := by omega
  have wrappedRoom : wrappedSeed + G.qLen ≤ usedBytes G.pLen := by unfold wrappedSeed usedBytes domainCheck; omega
  have wrappedStart : wrappedSeed < usedBytes G.pLen := by omega
  have stateRoom : VG.Impl.Dsa.Generation.Layout.hash + 512 + H.S ≤ usedBytes G.pLen := by
    have := K.hSB; unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [this]
  have workRoom : VG.Impl.Dsa.Generation.Layout.hash + K.Wb ≤ usedBytes G.pLen := by
    have := K.hWb; have hw := K.hW
    unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [this, hw]
  refine ⟨?_, offsetBound, T.fit, ?_, digest.trans len.symm, final.trans len.symm, ?_, ?_, ?_⟩
  · change T.bytes.length < 2 ^ 31
    rw [len]; omega
  · change (⟨T.pointer.setWidth 64, T.bytes.length⟩ : Region).Disjoint ⟨(G.pointer wrappedSeed).setWidth 64, T.bytes.length⟩
    rw [G.pointer_addr wrappedStart, len]
    have apart := T.part wrappedRoom
    rw [len] at apart
    exact apart
  · intro j hj r hr
    obtain ⟨outer, ho, sub⟩ := contributionWrites_sub K G T offset len final hj r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact G.frame_arena.sub_right sub
    · exact (G.frame_below (by decide : 48 ≤ 128)).sub_right sub
  · intro j hj r hr
    obtain ⟨outer, ho, sub⟩ := contributionWrites_sub K G T offset len final hj r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact T.arena.sub_right sub
    · exact (T.below (by decide : 48 ≤ 128)).sub_right sub
  · intro i hi j hj ne r hr
    change i ≤ G.contributionCount at hi
    change j ≤ G.contributionCount at hj
    rw [G.contribution_writes K T offset len final hj] at hr
    change (⟨((G.contributions T offset).output i).setWidth 64, T.bytes.length⟩ : Region).Disjoint r
    rw [G.contribution_address T offset len hi, len]
    have ir := G.contribution_room hi
    have ip := G.contribution_part hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact G.parts_disjoint ir wrappedRoom (.inr (by unfold wrappedSeed hashes; omega))
    · exact G.parts_disjoint ir stateRoom (.inr (by
        have := K.hSB; unfold VG.Impl.Dsa.Generation.Layout.hash hashes; omega_using [this]))
    · apply G.parts_disjoint ir (G.contribution_room hj)
      rcases qwidth with hq | hq <;> rw [hq] <;> omega
    · exact G.parts_disjoint ir workRoom (.inr (by
        have := K.hWb; have hw := K.hW
        unfold VG.Impl.Dsa.Generation.Layout.hash hashes; omega_using [this, hw]))
    · exact (G.stack_part_native ir (by decide : 48 ≤ 128)).symm
end VG.Proof.Dsa.X86.Generation
