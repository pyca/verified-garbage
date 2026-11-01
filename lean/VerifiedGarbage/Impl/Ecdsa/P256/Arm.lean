module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over P-256 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- P-256 as the code has it, its field multiplications by
`vg_p256_mul_mod_<p|n>_umaal` if `u`. -/
def p256With (u : Bool) : Cfg :=
  ⟨4, Spec.P256.curve, Impl.Weierstrass.Mont.p256p, Impl.Weierstrass.Mont.p256n, some Impl.Weierstrass.Mul.p256, u⟩

/-- P-256 as the code has it. -/
def p256 : Cfg := p256With false

/-- `vg_ecdsa_p256_sign`. -/
def signP256 : Prog isa := p256.sign

/-- `vg_p256_mul`, or with `u` `vg_p256_mul_umaal`. -/
def mulP256With (u : Bool) : Prog isa := (p256With u).mulFn

/-- `vg_p256_mul`. -/
def mulP256 : Prog isa := mulP256With false

/-- `vg_p256_mul_umaal`. -/
def mulP256U : Prog isa := mulP256With true

end VG.Impl.Ecdsa.Arm
