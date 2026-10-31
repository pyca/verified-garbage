module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over secp256k1 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- secp256k1 as the code has it. -/
def secp256k1 : Cfg := ⟨4, Spec.Secp256k1.curve, Spec.Weierstrass.Mont.secp256k1p, Spec.Weierstrass.Mont.secp256k1n, none, false⟩

/-- `vg_ecdsa_secp256k1_sign`. -/
def signSecp256k1 : Prog isa := secp256k1.sign

end VG.Impl.Ecdsa.Arm
