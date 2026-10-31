module

public import VerifiedGarbage.Proof.Ecdsa.Arm.MulVerified
public import VerifiedGarbage.Impl.Ecdsa.P384.Arm
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.MulVerified
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.UmaalLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.MulVerified
meta import VerifiedGarbage.Impl.Ecdsa.P384.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.MulVerified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.UmaalLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# P-384 on 32-bit ARM with `umaal`: the configuration, and `vg_p384_mul_umaal`

`p384With true`, P-384 with its field multiplications by
`vg_p384_mul_mod_<p|n>_umaal`, is a configuration the code supports
(`p384u_ok`: what `p384_ok` states, but that its `vg_p384_mul_umaal` has no
frame), and `vg_p384_mul_umaal` meets `vg_p384_mul`'s contract
(`mulU_verified`), constant time by taint tracking with `umaal` (`taintU`).
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.Arm.P384

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof

theorem p384u_ok : CfgOk (p384With true) where
  n0 := p384_ok.n0
  n10 := p384_ok.n10
  onG := p384_ok.onG
  p_odd := p384_ok.p_odd
  n_odd := p384_ok.n_odd
  p_lt := p384_ok.p_lt
  n_lt := p384_ok.n_lt
  n_enc := p384_ok.n_enc
  p_ge := p384_ok.p_ge
  n_ge := p384_ok.n_ge
  p_lt_2n := p384_ok.p_lt_2n
  minv_p := p384_ok.minv_p
  minv_n := p384_ok.minv_n
  len8 := p384_ok.len8
  len_lo := p384_ok.len_lo
  len_hi := p384_ok.len_hi
  sh := p384_ok.sh
  fp := p384_ok.fp
  fn := p384_ok.fn
  mulNf := fun _ _ => Impl.Ecdsa.Arm.mulP384U_noFrames

/-- Either configuration. -/
theorem p384With_ok (u : Bool) : CfgOk (p384With u) := by
  cases u
  · exact p384_ok
  · exact p384u_ok

namespace Mul

theorem mulU_ct : ConstantTime isa (mulArm C).pre (mulArm C).pub mulP384U :=
  VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0])
    (fun _ _ _ _ hp => Taint.agree_ofRegs fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.2) (by taint_decide)

/-- `vg_p384_mul_umaal` on 32-bit ARM. -/
theorem mulU_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified Arm.target mulP384U (C.mulInRangeContract Arm.abi) :=
  VG.Proof.Ecdsa.Arm.mul_verified (c := p384With true) (curve := "p384") (desc := "P-384") (saved := 1)
    p384u_ok hL mulU_ct ⟨_, sat_pre hL⟩

end Mul

end VG.Proof.Ecdsa.Arm.P384
