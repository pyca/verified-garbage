module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-! # ECDSA over P-224 on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE

/-- P-224 as the code has it. -/
def p224 : Cfg := ⟨4, Spec.P224.curve, Spec.Weierstrass.Mont.p224p, Spec.Weierstrass.Mont.p224n⟩

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.sign

end VG.Impl.Ecdsa.PPC64LE
