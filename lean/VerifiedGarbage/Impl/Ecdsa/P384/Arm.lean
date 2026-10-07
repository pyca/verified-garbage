import VerifiedGarbage.Impl.Ecdsa.Arm
import VerifiedGarbage.Spec.P384

/-! # ECDSA over P-384 on 32-bit ARM: six-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- P-384 as the code has it. -/
def p384 : Cfg := ⟨6, Spec.P384.curve, Spec.Weierstrass.Mont.p384p, Spec.Weierstrass.Mont.p384n⟩

/-- `vg_ecdsa_p384_sign`. -/
def signP384 : Prog isa := p384.sign

end VG.Impl.Ecdsa.Arm
