import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.CachedHead
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.CachedTail
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.DoubleRR
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.MixedAdd
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableHead
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableTail

/-! P-256 joint verification on AArch64 as a literal. Its forwarded field
programs, which the kernel evaluates slowly, have literals of their own
(`JointLit/`), checked in parallel, which this one reads. -/

namespace VG
materialize_code Impl.Ecdsa.Verify.AArch64.P256Joint.verify
end VG
