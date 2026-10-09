import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Program
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint

/-! The tail of the forwarded cached additions of P-256 joint verification, as a
literal (`Proof/Framework/Lit.lean`): `Forward.ArithmeticJacTail`'s. -/

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P256

noncomputable def cachedTail.lit : Prog isa := .block Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail.rightCode.lit

theorem cachedTail.lit_eq :
    VerifyArithmetic.program P256Joint.cfg.K.M
      (jacTail P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.E P256Joint.cfg.K.D) = cachedTail.lit :=
  (program_eq .jacTail).trans (congrArg Code.block Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail.optimized_lit)

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
