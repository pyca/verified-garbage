module

public import VerifiedGarbage.Proof.Ecdsa.Arm.MulVerified
public import VerifiedGarbage.Impl.Ecdsa.P224.Arm
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.MulVerified
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.UmaalLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.MulVerified
meta import VerifiedGarbage.Impl.Ecdsa.P224.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.MulVerified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.UmaalLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# P-224 on 32-bit ARM with `umaal`: the configuration, and `vg_p224_mul_umaal`

`p224With true`, P-224 with its field multiplications by
`vg_p224_mul_mod_<p|n>_umaal`, is a configuration the code supports
(`p224u_ok`: what `p224_ok` states, but that its `vg_p224_mul_umaal` has no
frame), and `vg_p224_mul_umaal` meets `vg_p224_mul`'s contract
(`mulU_verified`), constant time by taint tracking with `umaal` (`taintU`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P224

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof

theorem p224u_ok : CfgOk (p224With true) where
  n0 := p224_ok.n0
  n10 := p224_ok.n10
  onG := p224_ok.onG
  p_odd := p224_ok.p_odd
  n_odd := p224_ok.n_odd
  p_lt := p224_ok.p_lt
  n_lt := p224_ok.n_lt
  n_enc := p224_ok.n_enc
  p_ge := p224_ok.p_ge
  n_ge := p224_ok.n_ge
  p_lt_2n := p224_ok.p_lt_2n
  minv_p := p224_ok.minv_p
  minv_n := p224_ok.minv_n
  len8 := p224_ok.len8
  len_lo := p224_ok.len_lo
  len_hi := p224_ok.len_hi
  sh := p224_ok.sh
  fp := p224_ok.fp
  fn := p224_ok.fn
  mulNf := fun _ _ => Impl.Ecdsa.Arm.mulP224U_noFrames

/-- Either configuration. -/
theorem p224With_ok (u : Bool) : CfgOk (p224With u) := by
  cases u
  · exact p224_ok
  · exact p224u_ok

namespace Mul

theorem mulU_ct : ConstantTime isa (mulArm C).pre (mulArm C).pub mulP224U :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.2) (by taint_decide)

/-- `vg_p224_mul_umaal` on 32-bit ARM. -/
theorem mulU_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target mulP224U (C.mulInRangeContract Arm.abi) :=
  VG.Proof.Ecdsa.Arm.mul_verified (c := p224With true) (curve := "p224") (desc := "P-224") (saved := 1)
    p224u_ok hL mulU_ct ⟨_, sat_pre hL⟩

end Mul

end VG.Proof.Ecdsa.Arm.P224
