module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-! # ECDSA over P-224 on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE

/-- P-224 as the code has it. -/
def p224 : Cfg := ⟨4, Spec.P224.curve, Impl.Weierstrass.Mont.p224p, Impl.Weierstrass.Mont.p224n, some Impl.Weierstrass.Mul.p224⟩

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.sign

/-- `vg_p224_mul`. -/
def mulP224 : Prog isa := p224.mulFn

end VG.Impl.Ecdsa.PPC64LE
