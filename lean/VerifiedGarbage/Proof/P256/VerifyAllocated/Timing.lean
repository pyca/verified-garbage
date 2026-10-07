import VerifiedGarbage.Proof.P256.VerifyAllocated.Double
import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming

namespace VG.Proof.P256.VerifyAllocated
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64

theorem Double_ct : FieldCT (VG.Impl.P256.VerifyAllocated.program .doubleRR) := by
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem MixedHead_ct : FieldCT (VG.Impl.P256.VerifyAllocated.program .mixedHead) := by
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem MixedTail_ct : FieldCT (VG.Impl.P256.VerifyAllocated.program .mixedTail) := by
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem JacTail_ct : FieldCT (VG.Impl.P256.VerifyAllocated.program .jacTail) := by
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem CachedHead_ct : FieldCT (VG.Impl.P256.VerifyAllocated.program .cachedHead) := by
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.VerifyAllocated
