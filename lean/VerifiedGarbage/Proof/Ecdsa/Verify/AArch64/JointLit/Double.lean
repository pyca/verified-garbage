import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256RD
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated

/-! The forwarded point doubling of P-256 verification (`VerifyDouble.double`) as a
literal, checked once for the joint and allocated verifications, which call it
from their table, cached additions and mixed additions (`Proof/Framework/Lit.lean`):
`Forward.P256RD`'s, by rewriting, rather than the kernel running the optimizer
again. -/

namespace VG.Proof.Ecdsa.Verify.AArch64.JointLit
open VG VG.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P256

noncomputable def double.lit : Prog isa := .block Proof.Weierstrass.AArch64.Forward.P256Bounds.rightRD.lit

theorem double.lit_eq :
    VerifyDouble.double P256Joint.cfg.K.M P256Joint.cfg.K.S P256Joint.cfg.K.R P256Joint.cfg.K.D =
      double.lit := by
  change VerifyDouble.double VerifyDouble.M VerifyDouble.S VerifyDouble.R VerifyDouble.D = _
  rw [VerifyDouble.double, ite_eq_left (show VerifyDouble.selected VerifyDouble.M VerifyDouble.S
    VerifyDouble.R VerifyDouble.D from ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩)]
  exact congrArg Code.block Proof.Weierstrass.AArch64.Forward.P256RD.optimized_lit

/-- `double` as `P256Allocated.mixedAdd` writes it, with `P256Allocated.K`, which
is `P256Joint.cfg.K` by definition: `materialize_code` reads a literal where the
code has its left-hand side as written. -/
noncomputable abbrev doubleAllocated.lit := double.lit
theorem doubleAllocated.lit_eq :
    VerifyDouble.double P256Allocated.K.M P256Allocated.K.S P256Allocated.K.R P256Allocated.K.D =
      doubleAllocated.lit :=
  double.lit_eq

end VG.Proof.Ecdsa.Verify.AArch64.JointLit
