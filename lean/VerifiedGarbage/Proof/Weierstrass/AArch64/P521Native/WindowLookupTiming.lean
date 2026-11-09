module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupCode
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupCode
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.TCB.AArch64.Isa

/-! The full signed selection reveals only workspace, table, and public digit index. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64

theorem window_lookup_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19,.x26]))
      (.block windowLookupCode) := by
  exact VG.Taint.constantTime (A:=VG.AArch64.taint) (AArch64.Taint.ofRegs [.x0,.x19,.x26])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Weierstrass.AArch64.P521Native
