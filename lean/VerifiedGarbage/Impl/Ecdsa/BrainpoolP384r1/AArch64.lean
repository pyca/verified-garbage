module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mul

/-! # brainpoolP384r1 on AArch64, using complete general addition -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- Six-word arithmetic without a precomputed comb table. -/
def brainpoolp384r1 : Cfg := ⟨6, Spec.BrainpoolP384r1.curve, [], (0, 0), "", true,
  some Impl.Weierstrass.Inverse.brainpoolp384r1, none⟩

namespace BrainpoolP384r1

/-- `R = [k]G`, for the `k` in `K`'s slot, by a call of `vg_brainpoolp384r1_mul`. -/
def gMul : Prog isa := brainpoolp384r1.mulAt "vg_brainpoolp384r1_mul" GX GY

end BrainpoolP384r1

/-- `vg_ecdsa_brainpoolp384r1_sign`. -/
def signBrainpoolP384r1 : Prog isa := brainpoolp384r1.signWith BrainpoolP384r1.gMul

end VG.Impl.Ecdsa.AArch64
