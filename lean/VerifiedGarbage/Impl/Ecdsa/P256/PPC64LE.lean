module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-! # ECDSA over P-256 on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE

/-- P-256 as the code has it. -/
def p256 : Cfg := ⟨4, Spec.P256.curve, Spec.Weierstrass.Mont.p256p, Spec.Weierstrass.Mont.p256n⟩

/-- `vg_ecdsa_p256_sign`. -/
def signP256 : Prog isa := p256.sign

end VG.Impl.Ecdsa.PPC64LE
