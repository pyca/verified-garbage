module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
public import VerifiedGarbage.Impl.P256.VerifyAllocated
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
meta import VerifiedGarbage.Impl.P256.VerifyAllocated
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
meta import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
meta import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
meta import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

@[expose] public section

namespace VG.Proof.P256.VerifyAllocated
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64

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
