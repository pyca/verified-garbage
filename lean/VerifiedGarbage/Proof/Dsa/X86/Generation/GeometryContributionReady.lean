module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryContributions
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryHash

/-! # The saved seed and shared hash arena supply every p contribution -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem contributionReady {H : Hash} (K : HashOK H) {G : GenerationGeometry} {T : GenerationTape G}
    {offset : Nat} {s : State} {W : Nat → BitVec 32}
    (R : ArenaReady G s) (slots : FrameWords s.mem G.frameBase W)
    (len : T.bytes.length = G.qLen) (final : H.F = G.qLen)
    (source : W 1 = T.pointer) (wrapped : W 3 = G.pointer wrappedSeed)
    (hashesValue : W 4 = G.pointer hashes) (scratch : W 14 = G.pointer VG.Impl.Dsa.Generation.Layout.hash)
    (offsetValue : W 2 = BitVec.ofNat 32 offset)
    (sourceRead : ∀ i < T.bytes.length, InRegions (s.rd ++ s.wr) (off (T.pointer.setWidth 64) i) 1)
    (sourceBytes : ∀ i < T.bytes.length, s.mem (off (T.pointer.setWidth 64) i) = T.bytes.getD i 0) :
    ContributionReady K (G.contributions T offset) s := by
  have qwidth := G.qWidth
  have wrappedRoom : wrappedSeed + G.qLen ≤ usedBytes G.pLen := by unfold wrappedSeed usedBytes domainCheck; omega
  have wrappedStart : wrappedSeed < usedBytes G.pLen := by omega
  have hashRoom : VG.Impl.Dsa.Generation.Layout.hash + 8192 ≤ usedBytes G.pLen := by
    unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega
  refine ⟨R.frame, ?_, (slots 1 (by decide)).trans source, (slots 3 (by decide)).trans wrapped,
    (slots 4 (by decide)).trans hashesValue, (slots 14 (by decide)).trans scratch,
    (slots 2 (by decide)).trans offsetValue, ?_, sourceRead, ?_, sourceBytes⟩
  · change stk s = below G.frame 48
    unfold stk
    rw [R.frameReg]
  · intro j hj
    change j ≤ G.contributionCount at hj
    change HashResources K (G.pointer wrappedSeed) ((G.contributions T offset).output j)
      (G.pointer VG.Impl.Dsa.Generation.Layout.hash) T.bytes.length s
    rw [len, G.contribution_pointer T offset len j]
    apply hashArenaResources K R (by omega : G.qLen < 2 ^ 32) (G.pointer_fit wrappedStart wrappedRoom)
    · rw [G.pointer_addr wrappedStart]
      exact Covers.one (R.read wrappedRoom)
    · rw [G.pointer_addr wrappedStart]
      exact G.parts_disjoint wrappedRoom hashRoom (.inr (by unfold VG.Impl.Dsa.Generation.Layout.hash wrappedSeed; decide))
    · rw [G.pointer_addr wrappedStart]
      exact G.stack_part_native wrappedRoom (Nat.le_refl _)
    · rw [final]
      exact G.contribution_room hj
    · rw [final]
      exact G.parts_disjoint (G.contribution_room hj) hashRoom
        (.inr (by unfold VG.Impl.Dsa.Generation.Layout.hash hashes; omega))
  · intro i hi
    change i < T.bytes.length at hi
    rw [len] at hi
    exact R.writePointer wrappedStart wrappedRoom i 1 (by omega)
end VG.Proof.Dsa.X86.Generation
