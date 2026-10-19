module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.CachedHead
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.CachedTail
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.DoubleRR
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.MixedAdd
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableHead
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableTail
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.CachedHead
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.CachedTail
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.DoubleRR
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.MixedAdd
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableHead
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableTail
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

/-! P-256 joint verification on AArch64 as a literal. Its forwarded field
programs, which the kernel evaluates slowly, have literals of their own
(`JointLit/`), checked in parallel, which this one reads. -/

@[expose] public section

namespace VG
materialize_code Impl.Ecdsa.Verify.AArch64.P256Joint.verify
end VG
