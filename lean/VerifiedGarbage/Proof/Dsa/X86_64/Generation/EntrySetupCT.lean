module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Entry setup accesses only fixed offsets of the public stack pointer -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Dsa.X86_64.Generation

def EntryStackAgree (s t : State) : Prop := s.gpr .rsp = t.gpr .rsp

theorem entrySetup_ct : RelCT isa EntryStackAgree
    (.block (entryHeader ++ entryIncoming ++ entryDerived)) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.rsp])
  · intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact h
  · taint_decide

theorem entrySave_ct : RelCT isa EntryStackAgree (.block saveRegisters) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.rsp])
  · intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact h
  · taint_decide

theorem entryRestore_ct : RelCT isa EntryStackAgree (.block restoreRegisters) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs [.rsp])
  · intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact h
  · taint_decide

end VG.Proof.Dsa.X86_64.Generation
