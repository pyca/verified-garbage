module

public import VerifiedGarbage.Impl.Ecdsa.X86
public import VerifiedGarbage.Spec.P256

/-! # ECDSA over P-256 on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- P-256 as the code has it. -/
def p256 : Cfg where
  n := 4
  C := Spec.P256.curve
  SP := Spec.Weierstrass.Mont.p256p
  SN := Spec.Weierstrass.Mont.p256n

/-- `vg_ecdsa_p256_sign`. -/
def signP256 : Prog isa := p256.sign

end VG.Impl.Ecdsa.X86
