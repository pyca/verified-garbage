module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mul

/-! # p192 on AArch64, using complete general addition -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- Four-word arithmetic without a precomputed comb table. -/
def p192 : Cfg := ⟨4, Spec.P192.curve, [], (0, 0), "", true,
  some Impl.Weierstrass.Inverse.p192, none⟩

namespace P192

/-- `R = [k]G`, for the `k` in `K`'s slot, by a call of `vg_p192_mul`. -/
def gMul : Prog isa := p192.mulAt "vg_p192_mul" GX GY

end P192

/-- `vg_ecdsa_p192_sign`. -/
def signP192 : Prog isa := p192.signWith P192.gMul

end VG.Impl.Ecdsa.AArch64
