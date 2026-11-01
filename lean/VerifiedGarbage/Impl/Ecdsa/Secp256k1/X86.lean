module

public import VerifiedGarbage.Impl.Ecdsa.X86

/-! # ECDSA over secp256k1 on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86

open VG.X86

/-- secp256k1 as the code has it. -/
def secp256k1 : Cfg where
  n := 4
  C := Spec.Secp256k1.curve
  SP := Impl.Weierstrass.Mont.secp256k1p
  SN := Impl.Weierstrass.Mont.secp256k1n

/-- `vg_ecdsa_secp256k1_sign`. -/
def signSecp256k1 : Prog isa := secp256k1.sign

end VG.Impl.Ecdsa.X86
