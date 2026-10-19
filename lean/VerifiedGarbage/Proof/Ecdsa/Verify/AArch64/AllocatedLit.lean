module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Double
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Double
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

/-! P-256 verification with register-allocated arithmetic on AArch64 as a
literal, reading the literals of the forwarded field programs it shares with
the joint verification (`JointLit/`). -/

@[expose] public section

namespace VG
materialize_code Impl.Ecdsa.Verify.AArch64.P256Allocated.verify
end VG
