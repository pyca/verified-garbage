module

public import VerifiedGarbage.Impl.Ecdsa.X86
public import VerifiedGarbage.Spec.P192

/-! # ECDSA over P-192 on x86 (32-bit): three-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- P-192 as the code has it. -/
def p192 : Cfg where
  n := 3
  C := Spec.P192.curve
  SP := Spec.Weierstrass.Mont.p192p
  SN := Spec.Weierstrass.Mont.p192n

/-- `vg_ecdsa_p192_sign`. -/
def signP192 : Prog isa := p192.sign

end VG.Impl.Ecdsa.X86
