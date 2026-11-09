module

public import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public meta import VerifiedGarbage.Impl.Mont.AArch64.P521Field.Kernels
public meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public meta import VerifiedGarbage.TCB.AArch64.Isa

/-! The complete scalar doubling helper uses only public addresses and fixed control flow. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Field

theorem double_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x1,.x2])) doubleFn := by
  exact VG.Taint.constantTime (A:=VG.AArch64.taint) (AArch64.Taint.ofRegs [.x0,.x1,.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Mont.AArch64.P521Field
