import VerifiedGarbage.Impl.Ecdsa.Arm
import VerifiedGarbage.Spec.P224

/-! # ECDSA over P-224 on 32-bit ARM: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- P-224 as the code has it. -/
def p224 : Cfg := ⟨4, Spec.P224.curve, Spec.Weierstrass.Mont.p224p, Spec.Weierstrass.Mont.p224n⟩

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.sign

end VG.Impl.Ecdsa.Arm
