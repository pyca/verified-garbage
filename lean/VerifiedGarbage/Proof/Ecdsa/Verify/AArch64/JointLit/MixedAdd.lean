import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Double
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint

/-! The forwarded mixed addition of P-256 joint verification, as a literal
(`Proof/Framework/Lit.lean`), reading the literal of the doubling it calls. -/

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P256

materialize_code mixedAdd :=
  Joint.mixedAdd P256Joint.cfg.K P256Joint.cfg.K.R P256Joint.cfg.K.E P256Joint.cfg.K.D

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
