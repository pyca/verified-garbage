import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated

/-! The forwarded point doubling of P-256 verification (`VerifyDouble.double`) as a
literal, checked once for the joint and allocated verifications, which call it
from their table, cached additions and mixed additions (`Proof/Framework/Lit.lean`). -/

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P256

materialize_code double :=
  VerifyDouble.double P256Joint.cfg.K.M P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.D

/-- `double` as `P256Allocated.mixedAdd` writes it, with `P256Allocated.K`, which
is `P256Joint.cfg.K` by definition: `materialize_code` reads a literal where the
code has its left-hand side as written. -/
noncomputable abbrev doubleAllocated.lit := double.lit
theorem doubleAllocated.lit_eq :
    VerifyDouble.double P256Allocated.K.M P256Allocated.K.S P256Allocated.K.R P256Allocated.K.D =
      doubleAllocated.lit :=
  double.lit_eq

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
