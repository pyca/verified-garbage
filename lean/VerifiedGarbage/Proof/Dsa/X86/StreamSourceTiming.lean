module

public import VerifiedGarbage.Proof.Dsa.X86.PointerTiming
public import VerifiedGarbage.Proof.Dsa.X86.CoreStreamSource

/-! # Selecting and saving a public streaming source -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem streamSource_relCT (p : Pointer) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ pointerValue base s p = pointerValue base t p)
      (.block (Core.pointer p ++ ([.store (sc sourcePointer) .esi] : List Instr)))
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  apply RelCT.block_append
  exact RelCT.seq (pointer_relCT p base size hz) (checkedBlockInvariant (τ' := workspaceTaint true) rfl rfl)

end VG.Proof.Dsa.X86
