module

public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Framework.Offset

/-! # Restoring the cdecl registers and protecting the return address -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem return_stack_disjoint {sp : BitVec 32} (h : 108 ≤ sp.toNat) :
    Region.Disjoint ⟨sp.setWidth 64, 4⟩ (callStack sp) := by
  rw [callStack_eq h]
  intro x hx hc
  have hs := sp.isLt
  simp only [Region.Contains] at hx hc
  bv_omega

theorem outside_return {s t : State} {base : Addr} {size : Nat}
    (O : StackOutside (s.gpr .esp) base size s.mem t.mem)
    (apart : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨base, size⟩) (hsp : 108 ≤ (s.gpr .esp).toNat) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  apply Mem.readW_congr
  intro i hi
  have H := apart ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) (Offset.contains_base _ (by omega) (by omega))
  change ¬ (ofs base ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) + 1 ≤ size) at H
  exact O _ (by omega) (return_stack_disjoint hsp _ (Offset.contains_base _ (by omega) (by omega)))

theorem outputFrame_return {s t : State} {base out : Addr} {size len : Nat}
    (O : StackOutputFrame (s.gpr .esp) base out size len s.mem t.mem)
    (scratchApart : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨base, size⟩)
    (outApart : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨out, len⟩) (hsp : 108 ≤ (s.gpr .esp).toNat) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  apply Mem.readW_congr
  intro i hi
  have W := scratchApart ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) (Offset.contains_base _ (by omega) (by omega))
  have B := outApart ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) (Offset.contains_base _ (by omega) (by omega))
  change ¬ (ofs base ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) + 1 ≤ size) at W
  change ¬ (ofs out ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i) + 1 ≤ len) at B
  exact O _ (by omega) (by omega) (return_stack_disjoint hsp _ (Offset.contains_base _ (by omega) (by omega)))

theorem restored_abi {s t u : State} (R : Restored t u s.gpr Entry.savedRegisters)
    (sp : t.gpr .esp = s.gpr .esp)
    (ret : t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32) :
    abiPreserved s u := by
  refine ⟨?_, by rw [R.mem]; exact ret⟩
  intro reg hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact R.regs _ (by decide)
  · exact (R.other _ (by decide)).trans sp

end VG.Proof.Dsa.X86
