module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Impl.Ecdsa.AArch64.CombCall
public import VerifiedGarbage.Impl.P521.CombTable7

/-! # ECDSA over P-521 on AArch64: nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64

/-- P-521 as the code has it. -/
def p521 : Cfg := ⟨9, Spec.P521.curve, Impl.P521.p521Comb7, Impl.P521.p521Comb7Start, "VG_P521_COMB", true,
  some Impl.Weierstrass.Inverse.p521, none⟩

/-- The comb (`Cfg.combP`): the body of `vg_p521_comb`, which signatures and
public keys call. -/
def combP521 : Prog isa := p521.combP

/-- `[k]G`, by a call of `vg_p521_comb`: `x30` kept in lane 0 of `v27`, which the comb does not write. -/
def gMulP521 : Prog isa := combCall "vg_p521_comb" (.vec .v27) combP521

/-- `vg_ecdsa_p521_sign`. -/
def signP521 : Prog isa := p521.signWith gMulP521

end VG.Impl.Ecdsa.AArch64
