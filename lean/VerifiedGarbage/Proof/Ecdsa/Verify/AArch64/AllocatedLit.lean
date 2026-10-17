module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
meta import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Double
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Double
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableHead
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableHead
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableTail
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableTail
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! P-256 verification with register-allocated arithmetic on AArch64 as a
literal, reading the literals of the forwarded field programs it shares with
the joint verification (`JointLit/`). -/

@[expose] public section

namespace VG
materialize_code Impl.Ecdsa.Verify.AArch64.P256Allocated.verify
end VG
