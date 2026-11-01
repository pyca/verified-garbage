module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mul

/-! # brainpoolP256r1 on AArch64, using complete general addition -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- Four-word arithmetic without a precomputed comb table. -/
def brainpoolp256r1 : Cfg := ⟨4, Spec.BrainpoolP256r1.curve, [], (0, 0), "", true,
  some Impl.Weierstrass.Inverse.brainpoolp256r1, none⟩

namespace BrainpoolP256r1

/-- `R = [k]G`, for the `k` in `K`'s slot, by a call of `vg_brainpoolp256r1_mul`. -/
def gMul : Prog isa := brainpoolp256r1.mulAt "vg_brainpoolp256r1_mul" GX GY

end BrainpoolP256r1

/-- `vg_ecdsa_brainpoolp256r1_sign`. -/
def signBrainpoolP256r1 : Prog isa := brainpoolp256r1.signWith BrainpoolP256r1.gMul

end VG.Impl.Ecdsa.AArch64
