module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Impl.P384.CombTable7

/-! # P-384 on AArch64: six-word field elements and scalars, as the code has it -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64

/-- P-384 as the code has it. -/
def p384 : Cfg := ⟨6, Spec.P384.curve, Impl.P384.p384Comb7, Impl.P384.p384Comb7Start, "VG_P384_COMB", true,
  some Impl.Weierstrass.Inverse.p384, none⟩

end VG.Impl.Ecdsa.AArch64
