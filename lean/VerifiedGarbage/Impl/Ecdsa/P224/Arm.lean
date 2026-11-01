module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over P-224 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- P-224 as the code has it, its field multiplications by
`vg_p224_mul_mod_<p|n>_umaal` if `u`. -/
def p224With (u : Bool) : Cfg :=
  ⟨4, Spec.P224.curve, Impl.Weierstrass.Mont.p224p, Impl.Weierstrass.Mont.p224n, some Impl.Weierstrass.Mul.p224, u⟩

/-- P-224 as the code has it. -/
def p224 : Cfg := p224With false

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.sign

/-- `vg_p224_mul`, or with `u` `vg_p224_mul_umaal`. -/
def mulP224With (u : Bool) : Prog isa := (p224With u).mulFn

/-- `vg_p224_mul`. -/
def mulP224 : Prog isa := mulP224With false

/-- `vg_p224_mul_umaal`. -/
def mulP224U : Prog isa := mulP224With true

end VG.Impl.Ecdsa.Arm
