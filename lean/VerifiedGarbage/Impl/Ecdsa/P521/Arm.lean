import VerifiedGarbage.Impl.Ecdsa.Arm
import VerifiedGarbage.Spec.P521

/-! # ECDSA over P-521 on 32-bit ARM: nine-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- P-521 as the code has it. -/
def p521 : Cfg := ⟨9, Spec.P521.curve, Spec.Weierstrass.Mont.p521p, Spec.Weierstrass.Mont.p521n⟩

/-- `vg_ecdsa_p521_sign`. -/
def signP521 : Prog isa := p521.sign

end VG.Impl.Ecdsa.Arm
