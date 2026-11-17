module

public import VerifiedGarbage.Impl.Ecdsa.P192.Arm
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Contract
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Impl.Ecdsa.P192.Arm
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.TCB.Arm.Isa

/-!
# P-192 on 32-bit ARM with `umaal`: the configuration

`p192With true`, P-192 with its field multiplications by
`vg_p192_mul_mod_<p|n>_umaal`, is a configuration the code supports
(`p192u_ok`: what `p192_ok` states), and its signature is constant time
(`signU_ct`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm.P192

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof

theorem p192u_ok : CfgOk (p192With true) where
  n0 := p192_ok.n0
  n10 := p192_ok.n10
  onG := p192_ok.onG
  p_odd := p192_ok.p_odd
  n_odd := p192_ok.n_odd
  p_lt := p192_ok.p_lt
  n_lt := p192_ok.n_lt
  n_enc := p192_ok.n_enc
  p_ge := p192_ok.p_ge
  n_ge := p192_ok.n_ge
  p_lt_2n := p192_ok.p_lt_2n
  minv_p := p192_ok.minv_p
  minv_n := p192_ok.minv_n
  len8 := p192_ok.len8
  len_lo := p192_ok.len_lo
  len_hi := p192_ok.len_hi
  sh := p192_ok.sh
  fp := p192_ok.fp
  fn := p192_ok.fn
  mulNf := fun _ h => nomatch h

/-- Either configuration. -/
theorem p192With_ok (u : Bool) : CfgOk (p192With u) := by
  cases u
  · exact p192_ok
  · exact p192u_ok

theorem signU_ct : ConstantTime isa signArm.pre signArm.pub signP192U :=
  VG.Taint.constantTime (A := taintU) τ₁ (fun _ _ hs ht h => agree_τ₁ hs ht h) (by taint_decide)

end VG.Proof.Ecdsa.Arm.P192
