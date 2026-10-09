import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowStoredField

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_all_fields {m : Mem} {work challenge secret out aux : Addr} {g : Nat}
    (hg : IsG g) (c : LowConstants)
    (hscale : ∀e<4,vword c.scale e=BitVec.ofNat 32 (2*g))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let result := (lowPassData g work out aux c d 8).mem
    ∀j<2,∀k<n,
      (coeffAt result (pairPolyPtr out j) k).toNat=
          (highBits g (pairedDifference m challenge secret out j)[k]!).toNat ∧
        (coeffAt result (pairPolyPtr aux j) k).toInt=
          lowBits g (pairedDifference m challenge secret out j)[k]! := by
  dsimp only
  intro j hj k hk
  have hkn : k<256 := hk
  have hu : k%32/4<8 := by omega
  have hi : k/64<4 := by omega
  have hh : k%64/32<2 := by omega
  have he : k%4<4 := by omega
  have hv := lowPass_stored_field hu he hg (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩ c
    (hscale _ he) hc hs ho ha hd hp hy flags count
  have hidx : lowCoeff (k%32/4) (⟨j,hj⟩,⟨k/64,hi⟩) ⟨k%64/32,hh⟩ (k%4)=k := by
    change 4*(k%32/4)+64*(k/64)+32*(k%64/32)+k%4=k
    have hm : k%64%32=k%32 := Nat.mod_mod_of_dvd k (by decide : 32∣64)
    have hm4 : k%32%4=k%4 := Nat.mod_mod_of_dvd k (by decide : 4∣32)
    omega
  simpa only [hidx] using hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired
