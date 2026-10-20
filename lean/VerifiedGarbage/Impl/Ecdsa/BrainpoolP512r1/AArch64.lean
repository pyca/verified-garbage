module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Spec.Weierstrass.Mul

/-! # brainpoolP512r1 on AArch64, using complete general addition -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- Eight-word arithmetic without a precomputed comb table. -/
def brainpoolp512r1 : Cfg := ⟨8, Spec.BrainpoolP512r1.curve, [], (0, 0), "", true,
  some Spec.Weierstrass.Inverse.brainpoolp512r1, none⟩

namespace BrainpoolP512r1

/-- `R = [k]G`, for the `k` in `K`'s slot, by a call of `vg_brainpoolp512r1_mul`. -/
def gMul : Prog isa := brainpoolp512r1.mulAt Spec.Weierstrass.Mul.brainpoolp512r1.mulApi.name GX GY

end BrainpoolP512r1

/-- `vg_ecdsa_brainpoolp512r1_sign`. -/
def signBrainpoolP512r1 : Prog isa := brainpoolp512r1.signWith BrainpoolP512r1.gMul

end VG.Impl.Ecdsa.AArch64
