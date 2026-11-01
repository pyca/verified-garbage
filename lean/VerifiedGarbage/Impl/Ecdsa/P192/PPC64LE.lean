module

public import VerifiedGarbage.Impl.Ecdsa.PPC64LE

/-! # ECDSA over P-192 on PPC64LE: three-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.PPC64LE

open VG.PPC64LE

/-- P-192 as the code has it. -/
def p192 : Cfg := ⟨3, Spec.P192.curve, Impl.Weierstrass.Mont.p192p, Impl.Weierstrass.Mont.p192n, none⟩

/-- `vg_ecdsa_p192_sign`. -/
def signP192 : Prog isa := p192.sign

end VG.Impl.Ecdsa.PPC64LE
