module

public import VerifiedGarbage.Impl.Ecdsa.P256.Arm
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.UmaalLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Impl.Ecdsa.P256.Arm
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.UmaalLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact

/-!
# P-256 on 32-bit ARM with `umaal`: the configuration

`p256With true`, P-256 with its field multiplications by
`vg_p256_mul_mod_<p|n>_umaal`, is a configuration the code supports
(`p256u_ok`: what `p256_ok` states, but that its `vg_p256_mul_umaal` has no
frame).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P256

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof

theorem p256u_ok : CfgOk (p256With true) where
  n0 := p256_ok.n0
  n10 := p256_ok.n10
  onG := p256_ok.onG
  p_odd := p256_ok.p_odd
  n_odd := p256_ok.n_odd
  p_lt := p256_ok.p_lt
  n_lt := p256_ok.n_lt
  n_enc := p256_ok.n_enc
  p_ge := p256_ok.p_ge
  n_ge := p256_ok.n_ge
  p_lt_2n := p256_ok.p_lt_2n
  minv_p := p256_ok.minv_p
  minv_n := p256_ok.minv_n
  len8 := p256_ok.len8
  len_lo := p256_ok.len_lo
  len_hi := p256_ok.len_hi
  sh := p256_ok.sh
  fp := p256_ok.fp
  fn := p256_ok.fn
  mulNf := fun _ _ => Impl.Ecdsa.Arm.mulP256U_noFrames

/-- Either configuration. -/
theorem p256With_ok (u : Bool) : CfgOk (p256With u) := by
  cases u
  · exact p256_ok
  · exact p256u_ok

end VG.Proof.Ecdsa.Arm.P256
