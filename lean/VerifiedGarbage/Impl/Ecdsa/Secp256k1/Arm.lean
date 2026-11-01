module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over secp256k1 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- secp256k1 as the code has it, its field multiplications by
`vg_secp256k1_mul_mod_<p|n>_umaal` if `u`. -/
def secp256k1With (u : Bool) : Cfg :=
  ⟨4, Spec.Secp256k1.curve, Impl.Weierstrass.Mont.secp256k1p, Impl.Weierstrass.Mont.secp256k1n, none, u⟩

/-- secp256k1 as the code has it. -/
def secp256k1 : Cfg := secp256k1With false

/-- `vg_ecdsa_secp256k1_sign`. -/
def signSecp256k1 : Prog isa := secp256k1.sign

end VG.Impl.Ecdsa.Arm
