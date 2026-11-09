module

public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public meta import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public meta import VerifiedGarbage.TCB.AArch64.Isa

/-! The complete scalar mixed-addition helper leaks no coordinate or condition flag. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Field

/-- Only the workspace and three public slot offsets must agree; field memory,
working registers, SIMD registers and condition flags may contain secrets. -/
theorem mixed_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x1,.x2,.x3])) mixedFn := by
  exact VG.Taint.constantTime (A:=VG.AArch64.taint) (AArch64.Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Mont.AArch64.P521Field
