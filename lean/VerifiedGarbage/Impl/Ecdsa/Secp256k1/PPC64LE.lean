module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-! # ECDSA over secp256k1 on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE

/-- secp256k1 as the code has it. -/
def secp256k1 : Cfg := ⟨4, Spec.Secp256k1.curve, Impl.Weierstrass.Mont.secp256k1p, Impl.Weierstrass.Mont.secp256k1n, none⟩

end VG.Impl.Ecdsa.PPC64LE
