module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over P-384 on 32-bit ARM: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- P-384 as the code has it, its field multiplications by
`vg_p384_mul_mod_<p|n>_umaal` if `u`. -/
def p384With (u : Bool) : Cfg :=
  ⟨6, Spec.P384.curve, Impl.Weierstrass.Mont.p384p, Impl.Weierstrass.Mont.p384n, some Impl.Weierstrass.Mul.p384, u⟩

/-- P-384 as the code has it. -/
def p384 : Cfg := p384With false

/-- `vg_ecdsa_p384_sign`. -/
def signP384 : Prog isa := p384.sign

/-- `vg_p384_mul`, or with `u` `vg_p384_mul_umaal`. -/
def mulP384With (u : Bool) : Prog isa := (p384With u).mulFn

/-- `vg_p384_mul`. -/
def mulP384 : Prog isa := mulP384With false

/-- `vg_p384_mul_umaal`. -/
def mulP384U : Prog isa := mulP384With true

end VG.Impl.Ecdsa.Arm
