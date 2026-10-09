import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLaneField

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_stored_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : LowIndex) (h : Fin 2) (c : LowConstants)
    (hscale : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let result := (lowPassData g work out aux c d 8).mem
    (coeffAt result (pairPolyPtr out i.1.val) (lowCoeff u i h e)).toNat=
        (highBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]!).toNat ∧
      (coeffAt result (pairPolyPtr aux i.1.val) (lowCoeff u i h e)).toInt=
        lowBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]! := by
  dsimp only
  have hv := lowLane_field hu he hg i h c hscale hc hs ho.symm hp hy
  constructor
  · rw [pairPolyPtr,←lowAddr_coeff _ out u i h he,
      lowPass_read_high g work out aux c _ (by decide : 8≤8) hu i h ho ha hd]
    exact hv.1
  · rw [pairPolyPtr,←lowAddr_coeff _ aux u i h he,
      lowPass_read_low g work out aux c _ (by decide : 8≤8) hu i h ho ha hd]
    exact hv.2

end VG.Proof.MlDsa.AArch64.Optimized.Paired
