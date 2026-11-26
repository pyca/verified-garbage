module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Impl.Ecdsa.AArch64.CombCall
public import VerifiedGarbage.Impl.P224.CombTable7

/-! # ECDSA over P-224 on AArch64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG.AArch64

/-- P-224 as the code has it. -/
def p224 : Cfg := ⟨4, Spec.P224.curve, Impl.P224.p224Comb7, Impl.P224.p224Comb7Start, "VG_P224_COMB", true,
  some Impl.Weierstrass.Inverse.p224, some Impl.Weierstrass.PointOps.p224⟩

/-- The comb (`Cfg.combP`): the body of `vg_p224_comb`, which signatures and
public keys call. -/
def combP224 : Prog isa := p224.combP

/-- `[k]G`, by a call of `vg_p224_comb`: `x30` kept in `x14`, which the comb does not write. -/
def gMulP224 : Prog isa := combCall "vg_p224_comb" (.gpr .x14) combP224

/-- `vg_ecdsa_p224_sign`. -/
def signP224 : Prog isa := p224.signWith gMulP224

/-- `vg_p224_proj_add`, which P-224's code calls for its complete additions. -/
def projAddP224 : Prog isa := p224.projAddFn

/-- The shared variable-base window body used by ECDH and signature verification. -/
def windowP224 : Prog isa := VG.Impl.Weierstrass.AArch64.WinCfg.window (p224.winCfg RM SS) p224.padd

/-- Call the window body, saving the outer return address above its vector temporaries. -/
def windowCallP224 : Prog isa :=
  .seq (.block [.vop (.ins .d2 .v29 1 .x30)])
    (.seq (.call "vg_p224_window" windowP224) (.block [.umov .x .x30 .v29 1]))

end VG.Impl.Ecdsa.AArch64
