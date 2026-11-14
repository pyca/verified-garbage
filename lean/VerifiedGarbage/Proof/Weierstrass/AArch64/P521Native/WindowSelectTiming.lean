module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.TCB.AArch64.Isa

/-! Both zero tests and both exceptional selections operate on secret field data. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

theorem window_select_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0]))
      (.block outerBlock143) := by
  exact VG.Taint.constantTime (A:=VG.AArch64.taint) (AArch64.Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Weierstrass.AArch64.P521Native
