module

public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

/-! # Secret arithmetic blocks preserve the public exponent counter -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

theorem exponentMask_taint (exp mask : Nat) :
    taint.checkBlock (workspaceTaint true) (exponentMask exp mask) = some (workspaceTaint true) := by
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
  change taint.checkBlock (workspaceTaint true)
    [.mov .ecx (.mem (sc 0)), .alu .and .ecx (.imm 0), .mov .eax (.imm 0),
      .alu .sub .eax (.reg .ecx), .store (sc 0) .eax] = _
  rfl

end VG.Proof.Mont.X86.Dynamic
