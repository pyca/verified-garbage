module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashResources
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers

/-! # Share one streaming-hash workspace across q and every p contribution -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.Generation.Layout VG.Impl.Pbkdf2.Stream.X86
open VG.Proof.Pbkdf2.Stream.X86

theorem hashArenaResources {G : GenerationGeometry} {s : State} {H : Hash} (K : HashOK H)
    (R : ArenaReady G s) {input : BitVec 32} {len output : Nat}
    (length : len < 2 ^ 32) (inputFit : input.toNat + len ≤ 2 ^ 32)
    (inputRead : Covers [⟨input.setWidth 64, len⟩] (s.rd ++ s.wr))
    (inputHash : Region.Disjoint ⟨input.setWidth 64, len⟩ (G.part VG.Impl.Dsa.Generation.Layout.hash 8192))
    (stackInput : (below G.frame 128).Disjoint ⟨input.setWidth 64, len⟩)
    (outputRoom : output + H.F ≤ usedBytes G.pLen)
    (outputHash : (G.part output H.F).Disjoint (G.part VG.Impl.Dsa.Generation.Layout.hash 8192)) :
    HashResources K input (G.pointer output) (G.pointer VG.Impl.Dsa.Generation.Layout.hash) len s := by
  have hashRoom : VG.Impl.Dsa.Generation.Layout.hash + 8192 ≤ usedBytes G.pLen := by
    unfold VG.Impl.Dsa.Generation.Layout.hash usedBytes domainCheck; omega
  have stateRoom : VG.Impl.Dsa.Generation.Layout.hash + 512 + H.S ≤ usedBytes G.pLen := by omega_using [hashRoom, K.hSB]
  have workRoom : VG.Impl.Dsa.Generation.Layout.hash + K.Wb ≤ usedBytes G.pLen := by omega_using [hashRoom, K.hWb, K.hW]
  have stateSub := G.subarea (d := VG.Impl.Dsa.Generation.Layout.hash) (e := 512) (n := H.S)
    (total := 8192) (by have := K.hSB; omega)
  have workSub : Region.Sub (G.part VG.Impl.Dsa.Generation.Layout.hash K.Wb) (G.part VG.Impl.Dsa.Generation.Layout.hash 8192) := by
    have sub := G.subarea (d := VG.Impl.Dsa.Generation.Layout.hash) (e := 0) (n := K.Wb) (total := 8192)
      (by have := K.hWb; have := K.hW; omega)
    simpa only [Nat.add_zero] using sub
  have sp : 48 ≤ (s.gpr .esp).toNat := by rw [R.frameReg]; have := G.stackSize; omega
  have outPos : output < usedBytes G.pLen := by have := K.hD0; have := K.hDF; omega
  have scratchPos : VG.Impl.Dsa.Generation.Layout.hash < usedBytes G.pLen := by omega
  have statePos : VG.Impl.Dsa.Generation.Layout.hash + 512 < usedBytes G.pLen := by omega_using [stateRoom, K.hS0]
  have stateAddr : (G.pointer VG.Impl.Dsa.Generation.Layout.hash + 512#32).setWidth 64 =
      off G.base (VG.Impl.Dsa.Generation.Layout.hash + 512) := by rw [G.pointer_add, G.pointer_addr statePos]
  have scratchAddr := G.pointer_addr scratchPos
  have outputAddr := G.pointer_addr outPos
  have stackEq : stk s = below G.frame 48 := by unfold stk; rw [R.frameReg]
  refine ⟨length, sp, inputRead, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, inputFit, ?_, ?_⟩
  · rw [stateAddr]; exact R.coversPart stateRoom
  · rw [stateAddr, scratchAddr]; exact Covers.pair (R.coversPart stateRoom) (R.coversPart workRoom)
  · rw [stateAddr, outputAddr, scratchAddr]
    exact (R.coversPart stateRoom).cons (Covers.pair (R.coversPart outputRoom) (R.coversPart workRoom))
  · rw [stateAddr, scratchAddr]
    exact G.parts_disjoint stateRoom workRoom (.inr (by omega_using [K.hWb, K.hW]))
  · rw [stateAddr]; exact inputHash.sub_right stateSub
  · rw [scratchAddr]; exact inputHash.sub_right workSub
  · rw [stateAddr, outputAddr]; exact (outputHash.sub_right stateSub).symm
  · rw [outputAddr, scratchAddr]; exact outputHash.sub_right workSub
  · rw [stackEq, stateAddr]; exact G.stack_part_native stateRoom (by decide)
  · rw [stackEq]; exact stackInput.sub_left (below_sub (by decide) G.stackSize)
  · rw [stackEq, outputAddr]; exact G.stack_part_native outputRoom (by decide)
  · rw [stackEq, scratchAddr]; exact G.stack_part_native workRoom (by decide)
  · rw [G.pointer_add, G.pointer_toNat statePos]; omega_using [G.arenaBound, stateRoom]
  · rw [G.pointer_toNat outPos]; have := G.arenaBound; omega
  · rw [G.pointer_toNat scratchPos]; have := G.arenaBound; omega
end VG.Proof.Dsa.X86.Generation
