import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Double
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableHead
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.TableTail

/-! P-256 verification with register-allocated arithmetic on AArch64 as a
literal, reading the literals of the forwarded field programs it shares with
the joint verification (`JointLit/`). -/

namespace VG
materialize_code Impl.Ecdsa.Verify.AArch64.P256Allocated.verify
end VG
