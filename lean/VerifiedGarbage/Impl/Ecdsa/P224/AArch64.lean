module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Impl.P224.CombTable7

/-! # ECDSA over P-224 on AArch64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64

/-- P-224 as the code has it. -/
def p224 : Cfg := ⟨4, Spec.P224.curve, Impl.P224.p224Comb7, Impl.P224.p224Comb7Start, "VG_P224_COMB", true,
  some Impl.Weierstrass.Inverse.p224, some Impl.Weierstrass.PointOps.p224⟩

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.sign

/-- `vg_p224_proj_add`, which P-224's code calls for its complete additions. -/
def projAddP224 : Prog isa := p224.projAddFn

end VG.Impl.Ecdsa.AArch64
