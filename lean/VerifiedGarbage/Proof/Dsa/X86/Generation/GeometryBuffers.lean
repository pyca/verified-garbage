module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate

/-! # Native buffer pointers and nested subregions in the shared arena -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem GenerationGeometry.pointer_add (G : GenerationGeometry) (d e : Nat) :
    G.pointer d + BitVec.ofNat 32 e = G.pointer (d + e) := by
  simp only [GenerationGeometry.pointer, BitVec.ofNat_add, BitVec.add_assoc]

theorem GenerationGeometry.subarea (G : GenerationGeometry) {d e n total : Nat} (room : e + n ≤ total) :
    Region.Sub (G.part (d + e) n) (G.part d total) := by
  have sub := Offset.sub_base (off G.base d) room
  simpa only [GenerationGeometry.part, off, BitVec.ofNat_add, BitVec.add_assoc] using sub

theorem GenerationGeometry.stack_native (G : GenerationGeometry) :
    below G.frame 128 = ⟨G.frameBase - BitVec.ofNat 64 128, 128⟩ := by
  unfold below
  rw [VG.X86.Taint.sub_setWidth G.stackSize]
  rfl

theorem GenerationGeometry.stack_part_native (G : GenerationGeometry) {d n k : Nat}
    (room : d + n ≤ usedBytes G.pLen) (depth : k ≤ 128) :
    (below G.frame k).Disjoint (G.part d n) := by
  have separate := G.stack_part room
  rw [← G.stack_native] at separate
  exact separate.sub_left (below_sub depth G.stackSize)

theorem ArenaReady.coversPart {G : GenerationGeometry} {s : State} (R : ArenaReady G s)
    {d n : Nat} (room : d + n ≤ usedBytes G.pLen) : Covers [G.part d n] s.wr := Covers.one (R.write room)
theorem GenerationGeometry.pointer_fit (G : GenerationGeometry) {d n : Nat}
    (start : d < usedBytes G.pLen) (room : d + n ≤ usedBytes G.pLen) :
    (G.pointer d).toNat + n ≤ 2 ^ 32 := by
  rw [G.pointer_toNat start]
  have := G.arenaBound
  omega

theorem ArenaReady.readPointer {G : GenerationGeometry} {s : State} (R : ArenaReady G s)
    {d n : Nat} (start : d < usedBytes G.pLen) (room : d + n ≤ usedBytes G.pLen)
    (e k : Nat) (fits : e + k ≤ n) :
    InRegions (s.rd ++ s.wr) (off ((G.pointer d).setWidth 64) e) k := by
  rw [G.pointer_addr start]
  simpa only [off, BitVec.ofNat_add, BitVec.add_assoc] using
    (R.read (d := d + e) (n := k) (by omega))

theorem ArenaReady.writePointer {G : GenerationGeometry} {s : State} (R : ArenaReady G s)
    {d n : Nat} (start : d < usedBytes G.pLen) (room : d + n ≤ usedBytes G.pLen)
    (e k : Nat) (fits : e + k ≤ n) :
    InRegions s.wr (off ((G.pointer d).setWidth 64) e) k := by
  rw [G.pointer_addr start]
  simpa only [off, BitVec.ofNat_add, BitVec.add_assoc] using
    (R.write (d := d + e) (n := k) (by omega))
end VG.Proof.Dsa.X86.Generation
