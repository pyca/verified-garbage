module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mul

/-! # brainpoolP320r1 on AArch64, using complete general addition -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- Five-word arithmetic without a precomputed comb table. -/
def brainpoolp320r1 : Cfg := ⟨5, Spec.BrainpoolP320r1.curve, [], (0, 0), "", true,
  some Impl.Weierstrass.Inverse.brainpoolp320r1, none⟩

namespace BrainpoolP320r1

/-- `R = [k]G`, for the `k` in `K`'s slot, by a call of `vg_brainpoolp320r1_mul`. -/
def gMul : Prog isa := brainpoolp320r1.mulAt "vg_brainpoolp320r1_mul" GX GY

end BrainpoolP320r1

/-- `vg_ecdsa_brainpoolp320r1_sign`. -/
def signBrainpoolP320r1 : Prog isa := brainpoolp320r1.signWith BrainpoolP320r1.gMul

end VG.Impl.Ecdsa.AArch64
