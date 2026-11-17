module

public import VerifiedGarbage.Impl.Ecdsa.P521.Arm
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Contract
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.UmaalLit
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.Arm.MontModuli
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Impl.Ecdsa.P521.Arm
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.UmaalLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# P-521 on 32-bit ARM with `umaal`: the configuration

`p521With true`, P-521 with its field multiplications by
`vg_p521_mul_mod_<p|n>_umaal`, is a configuration the code supports
(`p521u_ok`: what `p521_ok` states, but that its `vg_p521_mul_umaal` has no
frame).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P521

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof VG.Proof.Weierstrass.Arm

theorem p521u_ok : CfgOk (p521With true) where
  n0 := by decide
  n10 := by decide
  onG := Proof.P521.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  n_enc := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by
    rw [show (p521With true).sh = 7 by
      unfold Cfg.sh
      rw [show Spec.Ecdsa.nBits (p521With true).C = 521 from p521_nBits]
      rfl]
    decide
  fp := ⟨rfl, rfl, Mont.p521p_ok, rfl⟩
  fn := ⟨rfl, rfl, Mont.p521n_ok, rfl⟩
  mulNf := fun _ _ => Impl.Ecdsa.Arm.mulP521U_noFrames

/-- Either configuration. -/
theorem p521With_ok (u : Bool) : CfgOk (p521With u) := by
  cases u
  · exact p521_ok
  · exact p521u_ok

end VG.Proof.Ecdsa.Arm.P521
