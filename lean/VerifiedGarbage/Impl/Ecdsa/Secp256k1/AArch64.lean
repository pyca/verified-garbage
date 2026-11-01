module

public import VerifiedGarbage.Impl.Ecdsa.AArch64
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mul

/-! # secp256k1 on AArch64, using complete general addition -/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- Four-word arithmetic without a precomputed comb table. -/
def secp256k1 : Cfg := ⟨4, Spec.Secp256k1.curve, [], (0, 0), "", true,
  some Impl.Weierstrass.Inverse.secp256k1, none⟩

namespace Secp256k1

/-- `R = [k]G`, for the `k` in `K`'s slot, by a call of `vg_secp256k1_mul`. -/
def gMul : Prog isa := secp256k1.mulAt "vg_secp256k1_mul" GX GY

end Secp256k1

/-- `vg_ecdsa_secp256k1_sign`. -/
def signSecp256k1 : Prog isa := secp256k1.signWith Secp256k1.gMul

end VG.Impl.Ecdsa.AArch64
