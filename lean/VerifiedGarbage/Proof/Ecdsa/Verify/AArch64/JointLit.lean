module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.CachedHead
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.CachedHead
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.CachedTail
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.CachedTail
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.DoubleRR
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.DoubleRR
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.MixedAdd
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.MixedAdd
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableHead
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableHead
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableTail
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableTail
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! P-256 joint verification on AArch64 as a literal. Its forwarded field
programs, which the kernel evaluates slowly, have literals of their own
(`JointLit/`), checked in parallel, which this one reads. -/

@[expose] public section

namespace VG
materialize_code Impl.Ecdsa.Verify.AArch64.P256Joint.verify
end VG
