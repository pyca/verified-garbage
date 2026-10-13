module

public import VerifiedGarbage.Impl.Ecdsa.X86
public import VerifiedGarbage.Spec.P521

/-! # ECDSA over P-521 on x86 (32-bit): nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- P-521 as the code has it. -/
def p521 : Cfg where
  n := 9
  C := Spec.P521.curve
  SP := Spec.Weierstrass.Mont.p521p
  SN := Spec.Weierstrass.Mont.p521n

/-- `vg_ecdsa_p521_sign`. -/
def signP521 : Prog isa := p521.sign

end VG.Impl.Ecdsa.X86
