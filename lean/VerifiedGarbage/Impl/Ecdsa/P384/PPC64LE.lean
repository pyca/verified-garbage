module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-! # ECDSA over P-384 on PPC64LE: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE

/-- P-384 as the code has it. -/
def p384 : Cfg := ⟨6, Spec.P384.curve, Impl.Weierstrass.Mont.p384p, Impl.Weierstrass.Mont.p384n, some Impl.Weierstrass.Mul.p384⟩

/-- `vg_ecdsa_p384_sign`. -/
def signP384 : Prog isa := p384.sign

/-- `vg_p384_mul`. -/
def mulP384 : Prog isa := p384.mulFn

end VG.Impl.Ecdsa.PPC64LE
