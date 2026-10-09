import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCoordinates

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.Spec.MlDsa

/-- The paired SIMD traversal covers exactly all coefficients of both polynomials. -/
theorem lowCoverage (P : Nat → Nat → Prop) :
    (∀e<4,∀u<8,∀i:LowIndex,∀h:Fin 2,P i.1.val (lowCoeff u i h e)) ↔
      ∀j<2,∀k<n,P j k := by
  constructor
  · intro hall j hj k hk
    have hkn : k<256 := hk
    have hu : k%32/4<8 := by omega
    have hi : k/64<4 := by omega
    have hh : k%64/32<2 := by omega
    have he : k%4<4 := by omega
    have hv := hall _ he _ hu (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩
    have hidx : lowCoeff (k%32/4) (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩ (k%4)=k := by
      change 4*(k%32/4)+64*(k/64)+32*(k%64/32)+k%4=k
      have hm : k%64%32=k%32 := Nat.mod_mod_of_dvd k (by decide : 32∣64)
      have hm4 : k%32%4=k%4 := Nat.mod_mod_of_dvd k (by decide : 4∣32)
      omega
    simpa only [hidx] using hv
  · intro hall e he u hu i h
    exact hall i.1.val i.1.isLt _ (lowCoeff_lt hu he i h)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
