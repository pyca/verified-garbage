import VerifiedGarbage.Impl.Ecdsa.Arm
import VerifiedGarbage.Spec.P256

/-! # ECDSA over P-256 on 32-bit ARM: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- P-256 as the code has it. -/
def p256 : Cfg := ⟨4, Spec.P256.curve, Spec.Weierstrass.Mont.p256p, Spec.Weierstrass.Mont.p256n⟩

/-- `vg_ecdsa_p256_sign`. -/
def signP256 : Prog isa := p256.sign

end VG.Impl.Ecdsa.Arm
