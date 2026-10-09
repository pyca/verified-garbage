import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Program
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint

/-! The head of the forwarded cached additions of P-256 joint verification, as a
literal (`Proof/Framework/Lit.lean`): `Forward.ArithmeticCachedHead`'s. -/

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P256

noncomputable def cachedHead.lit : Prog isa := .block Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead.rightCode.lit

theorem cachedHead.lit_eq :
    VerifyArithmetic.program P256Joint.cfg.K.M
      (CachedJac.head P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.E) = cachedHead.lit :=
  (program_eq .cachedHead).trans (congrArg Code.block Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead.optimized_lit)

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
