module

public import VerifiedGarbage.Proof.MlKem.AArch64.Lay
public import VerifiedGarbage.Impl.MlKem.AArch64.Noise
public import VerifiedGarbage.Impl.MlKem1024.AArch64.KeyGen

/-! # Scratch space for retained error polynomials

These are additional internal layout facts for the two concrete parameter
sets. They do not change either shared API contract or scratch size.
-/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.Impl.MlKem.AArch64

structure Room (P : KemLay) : Prop where
  kg : KG.SV P + 48 ≤ P.scl - 1024*P.k
  kem : KEM.SV P + 48 ≤ P.scl - 1024*P.k
  size : 1024*P.k ≤ P.scl

theorem room768 : Room lay768 := by constructor <;> decide +kernel
theorem room1024 : Room Impl.MlKem1024.AArch64.lay1024 := by constructor <;> decide +kernel

theorem noise_fits {P : KemLay} (hr : Room P) {i : Nat} (hi : i < P.k) :
    Impl.MlKem.AArch64.Noise.noiseOff P i + 1024 ≤ P.scl := by
  unfold Impl.MlKem.AArch64.Noise.noiseOff
  have hmul : 1024*(i+1) ≤ 1024*P.k := Nat.mul_le_mul_left _ hi
  have hs := hr.size
  omega

theorem noise_past_kg {P : KemLay} (hr : Room P) (i : Nat) :
    KG.SV P+48 ≤ Impl.MlKem.AArch64.Noise.noiseOff P i := by
  have := hr.kg
  unfold Impl.MlKem.AArch64.Noise.noiseOff
  omega

theorem noise_past_kem {P : KemLay} (hr : Room P) (i : Nat) :
    KEM.SV P+48 ≤ Impl.MlKem.AArch64.Noise.noiseOff P i := by
  have := hr.kem
  unfold Impl.MlKem.AArch64.Noise.noiseOff
  omega

end VG.Proof.MlKem.AArch64.Noise
