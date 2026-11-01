module

public import VerifiedGarbage.Impl.Ecdsa.Arm

/-! # ECDSA over P-521 on 32-bit ARM: nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm

open VG.Arm

/-- P-521 as the code has it. -/
def p521 : Cfg := ⟨9, Spec.P521.curve, Impl.Weierstrass.Mont.p521p, Impl.Weierstrass.Mont.p521n, some Impl.Weierstrass.Mul.p521, false⟩

/-- `vg_ecdsa_p521_sign`. -/
def signP521 : Prog isa := p521.sign

/-- `vg_p521_mul`. -/
def mulP521 : Prog isa := p521.mulFn

end VG.Impl.Ecdsa.Arm
