module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over P-521 on 32-bit ARM: nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- P-521 as the code has it, its field multiplications by
`vg_p521_mul_mod_<p|n>_umaal` if `u`. -/
def p521With (u : Bool) : Cfg :=
  ⟨9, Spec.P521.curve, Impl.Weierstrass.Mont.p521p, Impl.Weierstrass.Mont.p521n, some Impl.Weierstrass.Mul.p521, u⟩

/-- P-521 as the code has it. -/
def p521 : Cfg := p521With false

/-- `vg_ecdsa_p521_sign`. -/
def signP521 : Prog isa := p521.sign

/-- `vg_p521_mul`, or with `u` `vg_p521_mul_umaal`. -/
def mulP521With (u : Bool) : Prog isa := (p521With u).mulFn

/-- `vg_p521_mul`. -/
def mulP521 : Prog isa := mulP521With false

/-- `vg_p521_mul_umaal`. -/
def mulP521U : Prog isa := mulP521With true

/-- `vg_p521_mul_public`, or with `u` `vg_p521_mul_public_umaal`. -/
def mulPubP521With (u : Bool) : Prog isa := (p521With u).pubFn

/-- `vg_p521_mul_public`. -/
def mulPubP521 : Prog isa := mulPubP521With false

/-- `vg_p521_mul_public_umaal`. -/
def mulPubP521U : Prog isa := mulPubP521With true

end VG.Impl.Ecdsa.Arm
