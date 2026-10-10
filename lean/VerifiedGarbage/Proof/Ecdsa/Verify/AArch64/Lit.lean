import VerifiedGarbage.Proof.Weierstrass.AArch64.P256Literals
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256RD
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64

/-!
# ECDSA verification over P-256 on AArch64: the code as a literal

The field arithmetic is unrolled, so the kernel would build the instructions
again in every check that evaluates the code (constant time, properties of
every instruction): the literal of the code (`materialize_code`,
`Proof/Framework/Lit.lean`) is checked once here instead.

Its register-forwarded doubling (`VerifyDouble.double` from `R` to `D`, in
the window and, through the comb's own configuration, in the comb) is
`Forward.optimize`'s output, which `Forward.P256RD` already has as a
literal: `rd.lit_eq` and `rdComb.lit_eq` say so (by rewriting, not
evaluation), so that the literal of the code reads it rather than having
the kernel run the optimizer again.
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Proof.Weierstrass.AArch64

/-- The doubling from `R` to `D`, as `Forward.P256RD`'s literal. -/
noncomputable def rd.lit : Prog isa := .block Forward.P256Bounds.rightRD.lit

theorem rd.lit_eq : VG.Impl.P256.VerifyDouble.double
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg VG.Impl.Ecdsa.AArch64.p256).M
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg VG.Impl.Ecdsa.AArch64.p256).S
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg VG.Impl.Ecdsa.AArch64.p256).R
    (VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg VG.Impl.Ecdsa.AArch64.p256).D = rd.lit := by
  change VG.Impl.P256.VerifyDouble.double VG.Impl.P256.VerifyDouble.M VG.Impl.P256.VerifyDouble.S
    VG.Impl.P256.VerifyDouble.R VG.Impl.P256.VerifyDouble.D = _
  rw [VG.Impl.P256.VerifyDouble.double, ite_eq_left
    (show VG.Impl.P256.VerifyDouble.selected VG.Impl.P256.VerifyDouble.M VG.Impl.P256.VerifyDouble.S
      VG.Impl.P256.VerifyDouble.R VG.Impl.P256.VerifyDouble.D from ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩)]
  exact congrArg Code.block Forward.P256RD.optimized_lit

/-- The comb's doubling from its accumulator (`R`) to `D`, the same, as the
comb's configuration writes it. -/
noncomputable def rdComb.lit : Prog isa := .block Forward.P256Bounds.rightRD.lit

theorem rdComb.lit_eq : VG.Impl.P256.VerifyDouble.double
    (VG.Impl.Weierstrass.AArch64.Jacobian.combWinCfg (VG.Impl.Ecdsa.AArch64.Cfg.combCfg VG.Impl.Ecdsa.AArch64.p256)).M
    (VG.Impl.Weierstrass.AArch64.Jacobian.combWinCfg (VG.Impl.Ecdsa.AArch64.Cfg.combCfg VG.Impl.Ecdsa.AArch64.p256)).S
    (VG.Impl.Ecdsa.AArch64.Cfg.combCfg VG.Impl.Ecdsa.AArch64.p256).A
    (VG.Impl.Ecdsa.AArch64.Cfg.combCfg VG.Impl.Ecdsa.AArch64.p256).D = rdComb.lit := rd.lit_eq

end VG.Proof.Ecdsa.Verify.AArch64

namespace VG

materialize_code Impl.Ecdsa.Verify.AArch64.verifyP256

end VG
