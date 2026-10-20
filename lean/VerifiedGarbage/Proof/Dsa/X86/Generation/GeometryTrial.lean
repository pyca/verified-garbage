module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryBuffers

/-! # Trial division uses the persistent reciprocal table and a 16-byte call frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem allocated_trial_frame {s : State} (sp : 16 ≤ (s.gpr .esp).toNat) :
    TrialFrame (allocated 16 s) ((s.gpr .esp - 16).setWidth 64) := by
  refine ⟨by rw [allocated_esp]; rfl, by rw [allocated_wr]; exact List.mem_cons_self, ?_⟩
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide : 2 ^ 32 ≤ 2 ^ 64))]
  rw [BitVec.toNat_sub]
  have := (s.gpr .esp).isLt
  change (2 ^ 32 - 16 + (s.gpr .esp).toNat) % 2 ^ 32 + 16 ≤ 2 ^ 32
  omega

theorem allocated_read_region {s : State} {address : Addr} {len : Nat}
    (read : InRegions (s.rd ++ s.wr) address len) : InRegions ((allocated 16 s).rd ++ (allocated 16 s).wr) address len := by
  obtain ⟨r, hr, contains⟩ := read
  refine ⟨r, ?_, contains⟩
  change r ∈ s.rd ++ _ :: s.wr
  rcases List.mem_append.mp hr with hr | hr
  · exact List.mem_append_left _ hr
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)

theorem generationTrialInputs {G : GenerationGeometry} {s : State} {len offset entries : Nat}
    (R : ArenaReady G s) (positive : 2 ≤ len) (even : len % 2 = 0) (lenBound : len < 2 ^ 32)
    (entryPositive : 1 ≤ entries) (entryBound : entries ≤ 1024)
    (room : offset + len ≤ usedBytes G.pLen) (table : TrialTableReady s.mem G.base 1024) :
    TrialInputs (allocated 16 s) ((G.frame - 16).setWidth 64) (G.pointer offset) G.parent len entries := by
  have st : offset < usedBytes G.pLen := by omega
  have tr : 0 + 8 * entries ≤ usedBytes G.pLen := by unfold usedBytes domainCheck; omega
  have small : 16 ≤ (s.gpr .esp).toNat := by rw [R.frameReg]; have := G.stackSize; omega
  have frame : TrialFrame (allocated 16 s) ((G.frame - 16).setWidth 64) := by
    rw [← R.frameReg]
    exact allocated_trial_frame small
  refine ⟨frame, positive, even, lenBound, entryPositive, entryBound, G.pointer_fit st room, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := G.arenaBound
    unfold usedBytes domainCheck at *
    omega
  · intro i hi
    exact allocated_read_region (R.readPointer st room i 1 (by omega))
  · intro d hd
    exact allocated_read_region (R.read (d := d) (n := 4) (by omega))
  · rw [G.pointer_addr st]
    exact (G.stack_part_native room (by decide : 16 ≤ 128)).symm
  · have apart := (G.stack_part_native tr (by decide : 16 ≤ 128)).symm
    simpa only [GenerationGeometry.part, GenerationGeometry.base, below, off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using apart
  · exact ⟨fun i hi => table.prime i (by omega), fun i hi => table.reciprocal i (by omega)⟩

theorem GenerationGeometry.trial_frame_apart (G : GenerationGeometry) :
    (⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩ : Region).Disjoint ⟨(G.frame - 16).setWidth 64, 16⟩ := by
  apply Region.Disjoint.symm
  apply Offset.disjoint_of_le
  · change ((G.frame - 16).setWidth 64).toNat + 16 ≤ G.frameBase.toNat
    rw [G.frame_toNat, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide : 2 ^ 32 ≤ 2 ^ 64)), BitVec.toNat_sub]
    have := G.stackSize
    have := G.frame.isLt
    change (2 ^ 32 - 16 + G.frame.toNat) % 2 ^ 32 + 16 ≤ G.frame.toNat
    omega
  · change G.frameBase.toNat + VG.Impl.Dsa.X86.Generation.frameBytes ≤ 2 ^ 64
    rw [G.frame_toNat]
    have := G.frameBound
    omega
end VG.Proof.Dsa.X86.Generation
