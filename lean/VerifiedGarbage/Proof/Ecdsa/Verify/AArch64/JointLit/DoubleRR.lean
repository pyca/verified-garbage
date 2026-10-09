import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Program
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint

/-! The forwarded in-place doubling of P-256 joint verification, as a
literal (`Proof/Framework/Lit.lean`): `Forward.ArithmeticRR`'s. -/

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P256

noncomputable def doubleRR.lit : Prog isa := .block Proof.Weierstrass.AArch64.Forward.ArithmeticRR.rightCode.lit

theorem doubleRR.lit_eq :
    VerifyArithmetic.double P256Joint.cfg.K.M P256Joint.cfg.K.S P256Joint.cfg.K.R = doubleRR.lit :=
  (program_eq .doubleRR).trans (congrArg Code.block Proof.Weierstrass.AArch64.Forward.ArithmeticRR.optimized_lit)

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
