module

public import VerifiedGarbage.Proof.P256.VerifyAllocated.Double
meta import VerifiedGarbage.Proof.P256.VerifyAllocated.Double
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
meta import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
meta import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
meta import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
meta import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

@[expose] public section

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
