module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over P-192 on 32-bit ARM: three-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- P-192 as the code has it, its field multiplications by
`vg_p192_mul_mod_<p|n>_umaal` if `u`. -/
def p192With (u : Bool) : Cfg :=
  ⟨3, Spec.P192.curve, Impl.Weierstrass.Mont.p192p, Impl.Weierstrass.Mont.p192n,
    some Impl.Weierstrass.Mul.p192, u⟩

/-- P-192 as the code has it. -/
def p192 : Cfg := p192With false

/-- `vg_ecdsa_p192_sign`. -/
def signP192 : Prog isa := p192.sign

/-- `vg_p192_mul`, or with `u` `vg_p192_mul_umaal`. -/
def mulP192With (u : Bool) : Prog isa := (p192With u).mulFn

/-- `vg_p192_mul`. -/
def mulP192 : Prog isa := mulP192With false

/-- `vg_p192_mul_umaal`. -/
def mulP192U : Prog isa := mulP192With true

/-- `vg_p192_mul_public`, or with `u` `vg_p192_mul_public_umaal`. -/
def mulPubP192With (u : Bool) : Prog isa := (p192With u).pubFn

/-- `vg_p192_mul_public`. -/
def mulPubP192 : Prog isa := mulPubP192With false

/-- `vg_p192_mul_public_umaal`. -/
def mulPubP192U : Prog isa := mulPubP192With true

end VG.Impl.Ecdsa.Arm
