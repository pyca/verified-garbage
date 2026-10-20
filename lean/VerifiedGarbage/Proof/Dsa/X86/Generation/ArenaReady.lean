module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geometry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame

/-! # Arena and persistent frame permissions restored by every search phase -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.Generation.Layout

structure ArenaReady (G : GenerationGeometry) (s : State) : Prop where
  frame : SearchFrame s G.frameBase
  frameReg : s.gpr .esp = G.frame
  arenaWrite : (⟨G.base, usedBytes G.pLen⟩ : Region) ∈ s.wr
  arithmeticWrite : G.part arithmetic arithmeticBytes ∈ s.wr
  controlWrite : G.part control 12 ∈ s.wr

theorem ArenaReady.keep {G : GenerationGeometry} {s t : State} {regs : List Reg}
    (R : ArenaReady G s) (K : Keeps regs s t) (sp : .esp ∉ regs) : ArenaReady G t :=
  ⟨R.frame.keeps K sp, (K.1 _ sp).trans R.frameReg, by rw [K.2.2]; exact R.arenaWrite,
    by rw [K.2.2]; exact R.arithmeticWrite, by rw [K.2.2]; exact R.controlWrite⟩

theorem ArenaReady.write {G : GenerationGeometry} {s : State} (R : ArenaReady G s)
    {d n : Nat} (room : d + n ≤ usedBytes G.pLen) : InRegions s.wr (off G.base d) n :=
  ⟨_, R.arenaWrite, Offset.contains_base _ room (by have := G.arenaBound; omega)⟩

theorem ArenaReady.read {G : GenerationGeometry} {s : State} (R : ArenaReady G s)
    {d n : Nat} (room : d + n ≤ usedBytes G.pLen) : InRegions (s.rd ++ s.wr) (off G.base d) n := by
  obtain ⟨r, hr, hc⟩ := R.write room
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem ArenaReady.arithmeticScr {G : GenerationGeometry} {s : State} (R : ArenaReady G s)
    (edi : s.gpr .edi = G.pointer arithmetic) : Scr s (off G.base arithmetic) arithmeticBytes := by
  have room : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
  have small : arithmetic < usedBytes G.pLen := by unfold arithmetic usedBytes domainCheck; omega
  exact ⟨by rw [edi, G.pointer_addr small], R.arithmeticWrite, G.part_bound room,
    by rw [R.frameReg]; exact G.part_stk small room⟩

theorem ArenaReady.controlScr {G : GenerationGeometry} {s : State} (R : ArenaReady G s)
    (edi : s.gpr .edi = G.pointer control) : Scr s (off G.base control) 12 := by
  have room : control + 12 ≤ usedBytes G.pLen := by unfold VG.Impl.Dsa.Generation.Layout.control usedBytes domainCheck; omega
  have small : VG.Impl.Dsa.Generation.Layout.control < usedBytes G.pLen := by omega
  exact ⟨by rw [edi, G.pointer_addr small], R.controlWrite, G.part_bound room,
    by rw [R.frameReg]; exact G.part_stk small room⟩
end VG.Proof.Dsa.X86.Generation
