module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowSignedY
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowSignedY
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.TCB.AArch64.Isa

/-! Only the workspace and public window index determine signed-Y addresses. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64

theorem window_signed_y_constantTime :
    ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (AArch64.Taint.ofRegs [.x0,.x19]))
      (.block windowSignedY) := by
  exact VG.Taint.constantTime (A:=VG.AArch64.taint) (AArch64.Taint.ofRegs [.x0,.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Weierstrass.AArch64.P521Native
