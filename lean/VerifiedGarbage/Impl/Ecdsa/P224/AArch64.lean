module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Spec.P224
public import VerifiedGarbage.Impl.P224.CombTable7

/-! # ECDSA over P-224 on AArch64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64

/-- P-224 as the code has it. -/
def p224 : Cfg := ⟨4, Spec.P224.curve, Impl.P224.p224Comb7, Impl.P224.p224Comb7Start, "VG_P224_COMB", true⟩

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.sign

end VG.Impl.Ecdsa.AArch64
