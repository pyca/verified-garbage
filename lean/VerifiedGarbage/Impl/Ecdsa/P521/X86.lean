module

public import VerifiedGarbage.Impl.Ecdsa.X86

/-! # ECDSA over P-521 on x86 (32-bit): nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- P-521 as the code has it. -/
def p521 : Cfg where
  n := 9
  C := Spec.P521.curve
  SP := Impl.Weierstrass.Mont.p521p
  SN := Impl.Weierstrass.Mont.p521n
  mul := some Impl.Weierstrass.Mul.p521

end VG.Impl.Ecdsa.X86
