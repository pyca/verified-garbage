import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Double
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit.Program
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint

/-! The forwarded mixed addition of P-256 joint verification, as a literal
(`Proof/Framework/Lit.lean`): its field programs and the doubling it calls
are the literals of `Forward.ArithmeticMixedHead`, `Forward.ArithmeticMixedTail`
and `double`, by rewriting, rather than the kernel running the optimizer
again. -/

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P256

/-- `Joint.mixedAdd`, with the literals of its field programs and doubling. -/
noncomputable def mixedAdd.lit : Prog isa :=
  .seq (.block (zeroMask P256Joint.cfg.K.M.n P256Joint.cfg.K.R.z)) <|
  .ite (.nonzero .x .x2) (.block (copyPt P256Joint.cfg.K.M.n P256Joint.cfg.K.D P256Joint.cfg.K.E)) <|
  .seq (.block (copy P256Joint.cfg.K.M.n P256Joint.cfg.K.S.t2 P256Joint.cfg.K.R.x ++
    copy P256Joint.cfg.K.M.n P256Joint.cfg.K.S.t4 P256Joint.cfg.K.R.y)) <|
  .seq (.block Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead.rightCode.lit) <|
  .seq (.block (zeroMask P256Joint.cfg.K.M.n P256Joint.cfg.K.S.t3)) <|
  .ite (.nonzero .x .x2)
    (.seq (.block (zeroMask P256Joint.cfg.K.M.n P256Joint.cfg.K.S.t5)) <|
      .ite (.nonzero .x .x2) double.lit (.block (Jacobian.infinity P256Joint.cfg.K P256Joint.cfg.K.D)))
    (.block Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail.rightCode.lit)

theorem mixedAdd.lit_eq :
    Joint.mixedAdd P256Joint.cfg.K P256Joint.cfg.K.R P256Joint.cfg.K.E P256Joint.cfg.K.D = mixedAdd.lit := by
  have hH : VerifyArithmetic.program P256Joint.cfg.K.M
      (jacMixedHead P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.E) =
      .block Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead.rightCode.lit :=
    (program_eq .mixedHead).trans
      (congrArg Code.block Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead.optimized_lit)
  have hT : VerifyArithmetic.program P256Joint.cfg.K.M
      (jacMixedTail P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.E P256Joint.cfg.K.D) =
      .block Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail.rightCode.lit :=
    (program_eq .mixedTail).trans
      (congrArg Code.block Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail.optimized_lit)
  simp only [Joint.mixedAdd]
  rw [hH, hT, double.lit_eq]
  rfl

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
