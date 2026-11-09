module
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables

import VerifiedGarbage.Impl.MlKem.AArch64.Kem16

/-! # The 16-bit encryption noise

The noise of the 16-bit encryption, stored with 16 bits:
`ŷ` into `YH`, and `e₁` and `e₂` past the KEM's buffers (`ErrorsW`). -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

/-- `e₁` and `e₂`, stored with 16 bits past the KEM's buffers. -/
def ErrorsW (P : KemLay) (L : Layout) (s₀ : State) (rv : List Byte) (s : State) : Prop :=
  ∀j<P.k, PolyIsW 16 s.mem (sA L s₀ (Impl.MlKem.AArch64.Noise.noiseOff P j)) (cbd rv (P.k+j))

end VG.Proof.MlKem.AArch64.Kem
