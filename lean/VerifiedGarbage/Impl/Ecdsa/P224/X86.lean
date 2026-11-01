module

public import VerifiedGarbage.Impl.Ecdsa.X86

/-! # ECDSA over P-224 on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- P-224 as the code has it. -/
def p224 : Cfg where
  n := 4
  C := Spec.P224.curve
  SP := Impl.Weierstrass.Mont.p224p
  SN := Impl.Weierstrass.Mont.p224n
  mul := some Impl.Weierstrass.Mul.p224

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.sign

/-- `vg_p224_mul`. -/
def mulP224 : Prog isa := p224.mulFn

end VG.Impl.Ecdsa.X86
