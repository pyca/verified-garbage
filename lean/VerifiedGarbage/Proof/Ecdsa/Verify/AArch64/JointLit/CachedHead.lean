import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint

/-! The head of the forwarded cached additions of P-256 joint verification, as a
literal (`Proof/Framework/Lit.lean`). -/

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P256

materialize_code cachedHead :=
  VerifyArithmetic.program P256Joint.cfg.K.M
    (CachedJac.head P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.E)

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
