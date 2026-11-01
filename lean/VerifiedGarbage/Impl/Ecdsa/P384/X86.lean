module

public import VerifiedGarbage.Impl.Ecdsa.X86

/-! # ECDSA over P-384 on x86 (32-bit): six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- P-384 as the code has it. -/
def p384 : Cfg where
  n := 6
  C := Spec.P384.curve
  SP := Impl.Weierstrass.Mont.p384p
  SN := Impl.Weierstrass.Mont.p384n
  mul := some Impl.Weierstrass.Mul.p384

/-- `vg_ecdsa_p384_sign`. -/
def signP384 : Prog isa := p384.sign

/-- `vg_p384_mul`. -/
def mulP384 : Prog isa := p384.mulFn

end VG.Impl.Ecdsa.X86
