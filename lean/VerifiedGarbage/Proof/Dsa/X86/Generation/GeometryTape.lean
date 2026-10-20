module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geometry

/-! # Public seed, h, and witness tapes are disjoint from writable search storage -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.Mont VG.Impl.Dsa.Generation.Layout

structure GenerationTape (G : GenerationGeometry) where
  pointer : BitVec 32
  bytes : List Byte
  size : bytes.length < 2 ^ 32
  fit : pointer.toNat + bytes.length ≤ 2 ^ 32
  arena : Region.Disjoint ⟨pointer.setWidth 64, bytes.length⟩ ⟨G.base, usedBytes G.pLen⟩
  frame : Region.Disjoint ⟨pointer.setWidth 64, bytes.length⟩ ⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩
  stack : Region.Disjoint ⟨pointer.setWidth 64, bytes.length⟩ ⟨G.frameBase - BitVec.ofNat 64 128, 128⟩

theorem GenerationTape.part {G : GenerationGeometry} (T : GenerationTape G) {d n : Nat} (room : d + n ≤ usedBytes G.pLen) :
    Region.Disjoint ⟨T.pointer.setWidth 64, T.bytes.length⟩ (G.part d n) := T.arena.sub_right (G.part_sub room)
end VG.Proof.Dsa.X86.Generation
