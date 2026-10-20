module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PConstruct
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryContributions
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryContributionLayout

/-! # All p-construction resources follow from the concrete shared arena layout -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem generationPConstructInputs {H : Hash} (K : HashOK H) {G : GenerationGeometry} {T : GenerationTape G}
    {offset qvalue : Nat} {s : State}
    (R : ArenaReady G s) (C : ContributionReady K (G.contributions T offset) s)
    (len : T.bytes.length = G.qLen) (digest : H.D = G.qLen) (final : H.F = G.qLen)
    (offsetBound : offset + G.contributionCount < 2 ^ 24)
    (parent : s.mem.readW (off G.frameBase 20) 32 = G.parent)
    (qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off G.base q) G.qLen) = qvalue)
    (qpos : 0 < qvalue) (qbound : 2 * qvalue < 2 ^ (32 * (2 * (G.pLen / 8)))) :
    PConstructInputs K G (G.contributions T offset) qvalue s := by
  have pw := G.width
  have qw := G.qWidth
  have span := G.contribution_bounds.2
  have hr : hashes + (G.contributionCount + 1) * G.qLen ≤ usedBytes G.pLen := by
    unfold hashes usedBytes domainCheck; omega
  have hs : hashes < usedBytes G.pLen := by unfold hashes usedBytes domainCheck; omega
  have sr : shaped + G.pLen ≤ usedBytes G.pLen := by unfold shaped usedBytes domainCheck; omega
  have qr : q + G.qLen ≤ usedBytes G.pLen := by unfold q usedBytes domainCheck; omega
  let suffix := hashes + ((G.contributionCount + 1) * G.qLen - G.pLen)
  have suffixRoom : suffix + G.pLen ≤ usedBytes G.pLen := by dsimp only [suffix]; omega
  have suffixStart : suffix < usedBytes G.pLen := by omega
  have sourcePointer : (G.contributions T offset).hashes +
      BitVec.ofNat 32 (((G.contributions T offset).count + 1) * (G.contributions T offset).seed.length - G.pLen) = G.pointer suffix := by
    change G.pointer hashes + BitVec.ofNat 32 ((G.contributionCount + 1) * T.bytes.length - G.pLen) = _
    rw [len, G.pointer_add]
  refine ⟨R, C, contributionLayout K G T offset len digest final offsetBound, rfl, len, rfl,
    parent, qval, qpos, qbound, ?_, ?_, ?_, ?_, ?_⟩
  · change G.pLen ≤ (G.contributionCount + 1) * T.bytes.length
    rw [len]
    exact span.1
  · change (G.pointer hashes).toNat + (G.contributionCount + 1) * T.bytes.length ≤ 2 ^ 32
    rw [len]
    exact G.pointer_fit hs hr
  · rw [sourcePointer, G.pointer_addr suffixStart]
    exact G.parts_disjoint suffixRoom sr (.inl (by dsimp only [suffix]; unfold hashes shaped; omega))
  · intro i hi
    rw [sourcePointer]
    exact R.readPointer suffixStart suffixRoom i 1 (by omega)
  · intro r hr'
    obtain ⟨j, hj, writes⟩ := List.mem_flatMap.mp hr'
    have jbound : j ≤ G.contributionCount := by
      have := List.mem_range.mp hj
      change j < G.contributionCount + 1 at this
      omega
    rw [G.contribution_writes K T offset len final jbound] at writes
    have wrappedRoom : wrappedSeed + G.qLen ≤ usedBytes G.pLen := by unfold wrappedSeed usedBytes domainCheck; omega
    have stateRoom : VG.Impl.Dsa.Generation.Layout.hash + 512 + H.S ≤ usedBytes G.pLen := by
      have := K.hSB; unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [this]
    have workRoom : VG.Impl.Dsa.Generation.Layout.hash + K.Wb ≤ usedBytes G.pLen := by
      have := K.hWb; have hw := K.hW
      unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega_using [this, hw]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at writes
    rcases writes with rfl | rfl | rfl | rfl | rfl
    · exact G.parts_disjoint qr wrappedRoom (.inr (by unfold q wrappedSeed; omega))
    · exact G.parts_disjoint qr stateRoom (.inr (by
        have := K.hSB; unfold q VG.Impl.Dsa.Generation.Layout.hash; omega_using [this]))
    · exact G.parts_disjoint qr (G.contribution_room jbound) (.inr (by
        have := G.contribution_part jbound; unfold q hashes at *; omega_using [this]))
    · exact G.parts_disjoint qr workRoom (.inr (by
        have := K.hWb; have hw := K.hW
        unfold q VG.Impl.Dsa.Generation.Layout.hash; omega_using [this, hw]))
    · exact (G.stack_part_native qr (by decide : 48 ≤ 128)).symm
end VG.Proof.Dsa.X86.Generation
