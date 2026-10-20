module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PHashState
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers

/-! # Concrete contribution offsets and bounded wrapped-seed additions -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

def GenerationGeometry.contributionCount (G : GenerationGeometry) : Nat := (8 * G.pLen - 1) / (8 * G.qLen)

def GenerationGeometry.contributions (G : GenerationGeometry) (T : GenerationTape G) (offset : Nat) : ContributionPlan :=
  ⟨G.frameBase, T.pointer, G.pointer wrappedSeed, G.pointer hashes,
    G.pointer VG.Impl.Dsa.Generation.Layout.hash, T.bytes, G.contributionCount, offset, below G.frame 48⟩

theorem GenerationGeometry.contribution_bounds (G : GenerationGeometry) :
    G.contributionCount ≤ 11 ∧ G.pLen ≤ (G.contributionCount + 1) * G.qLen ∧
      (G.contributionCount + 1) * G.qLen ≤ 384 := by
  unfold contributionCount
  rcases G.lengths with h | h | h <;> rw [h.1, h.2] <;> decide

theorem GenerationGeometry.contribution_offset (G : GenerationGeometry) {counter : Nat} (bound : counter < 32 * G.pLen) :
    1 + counter * (G.contributionCount + 1) + G.contributionCount < 2 ^ 24 := by
  have width := G.width
  have count := G.contribution_bounds.1
  have product := Nat.mul_le_mul (by omega : counter ≤ 12288) (by omega : G.contributionCount + 1 ≤ 12)
  omega

theorem GenerationGeometry.contribution_part (G : GenerationGeometry) {j : Nat} (_hj : j ≤ G.contributionCount) :
    hashes + (G.contributionCount - j) * G.qLen + G.qLen ≤ hashes + 384 := by
  have bound := G.contribution_bounds.2.2
  have mult := Nat.mul_le_mul_right G.qLen (Nat.sub_le G.contributionCount j)
  rw [Nat.add_mul] at bound
  omega

theorem GenerationGeometry.contribution_room (G : GenerationGeometry) {j : Nat} (hj : j ≤ G.contributionCount) :
    hashes + (G.contributionCount - j) * G.qLen + G.qLen ≤ usedBytes G.pLen := by
  have := G.contribution_part hj
  unfold hashes usedBytes domainCheck at *
  omega

theorem GenerationGeometry.contribution_pointer (G : GenerationGeometry) (T : GenerationTape G) (offset : Nat)
    (len : T.bytes.length = G.qLen) (j : Nat) :
    ((G.contributions T offset).output j) = G.pointer (hashes + (G.contributionCount - j) * G.qLen) := by
  unfold contributions ContributionPlan.output
  rw [len, G.pointer_add]

theorem GenerationGeometry.contribution_address (G : GenerationGeometry) (T : GenerationTape G) (offset : Nat)
    (len : T.bytes.length = G.qLen) {j : Nat} (hj : j ≤ G.contributionCount) :
    ((G.contributions T offset).output j).setWidth 64 = off G.base (hashes + (G.contributionCount - j) * G.qLen) := by
  rw [G.contribution_pointer T offset len]
  exact G.pointer_addr (by have := G.contribution_room hj; have := G.qWidth; omega)

theorem GenerationGeometry.contribution_writes {H : Hash} (K : HashOK H) (G : GenerationGeometry)
    (T : GenerationTape G) (offset : Nat) (len : T.bytes.length = G.qLen) (final : H.F = G.qLen)
    {j : Nat} (hj : j ≤ G.contributionCount) :
    (G.contributions T offset).writes K j =
      [G.part wrappedSeed G.qLen, G.part (VG.Impl.Dsa.Generation.Layout.hash + 512) H.S,
       G.part (hashes + (G.contributionCount - j) * G.qLen) G.qLen,
       G.part VG.Impl.Dsa.Generation.Layout.hash K.Wb, below G.frame 48] := by
  have wrapped : wrappedSeed < usedBytes G.pLen := by unfold wrappedSeed usedBytes domainCheck; omega
  have hashStart : VG.Impl.Dsa.Generation.Layout.hash < usedBytes G.pLen := by
    unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega
  have stateStart : VG.Impl.Dsa.Generation.Layout.hash + 512 < usedBytes G.pLen := by
    unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega
  have output := G.contribution_address T offset len hj
  unfold ContributionPlan.writes
  rw [output]
  change [⟨(G.pointer wrappedSeed).setWidth 64, T.bytes.length⟩,
    ⟨(G.pointer VG.Impl.Dsa.Generation.Layout.hash + 512#32).setWidth 64, H.S⟩,
    ⟨off G.base (hashes + (G.contributionCount - j) * G.qLen), H.F⟩,
    ⟨(G.pointer VG.Impl.Dsa.Generation.Layout.hash).setWidth 64, K.Wb⟩, below G.frame 48] = _
  rw [len, final, G.pointer_addr wrapped, G.pointer_addr hashStart]
  have state : G.pointer VG.Impl.Dsa.Generation.Layout.hash + 512#32 = G.pointer (VG.Impl.Dsa.Generation.Layout.hash + 512) :=
    G.pointer_add _ _
  rw [state, G.pointer_addr stateStart]
  rfl
end VG.Proof.Dsa.X86.Generation
